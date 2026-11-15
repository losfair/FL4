/-
P3 (DESIGN.md §9), IO ports: **IOPortControl `Issue`** (FL4
`ioport::decode_control`, label 63) against l4v
`decode_ioport_control_invocation`, then `set_thread_state Restart` and
`arch_perform_invocation` (`perform_ioport_control_invocation`).

The range check is the bitmap's (`range_free_eq`) against the spec's
`is_ioport_range_free` (`IoRel`); the new IO port cap is inserted as a
child of the IO port control cap (`insert_ctl_full`), fresh because every
IO port cap's ports are allocated in the bitmap (`IoPortsAlloc`, l4v
`valid_ioports`). After the invocation the ports are allocated on both sides
(`IoRel.mask`).

Hypotheses beyond those of `CnodeCopy`: `IoLayout`, `IoRel`,
`IoPortsAlloc`; the invoked cap is the IO port control cap of a CNode slot;
the scheduler-action word is not a bitmap word.
-/
import Fl4Proofs.P3.IoPost
import Fl4Proofs.P3.IrqArch
import Fl4Proofs.P3.MdbStepVs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- Every IO port cap's ports are allocated (l4v `valid_ioports`). -/
def IoPortsAlloc (mem : U64 → U64) (kb : U64) (G : MdbGhost) : Prop :=
  ∀ y ∈ G.chains.flatten, ∀ f l owner, capV mem y = .IoPort f l owner →
    f.val ≤ l.val ∧ l.val < 65536 ∧ ∀ p, f.val ≤ p → p ≤ l.val → bitOf mem kb p = true

theorem srB_ioP_left (f l : U64) (b : capability.Cap) : srB (.IoPort f l 0#u64) b = decide (∃ owner, b = .IoPort f l owner) := by
  apply srB_of_eq; cases b <;> simp [objects.same_region_as]
  split_ifs <;> simp_all [eq_comm]

theorem io_fresh {mem : U64 → U64} {kb : U64} {G : MdbGhost} (hA : IoPortsAlloc mem kb G) {f l : U64}
    (hfl : f.val ≤ l.val) (hfree : ∀ p, f.val ≤ p → p ≤ l.val → bitOf mem kb p = false) :
    ∀ y ∈ G.chains.flatten, srB (.IoPort f l 0#u64) (capV mem y) = false := by
  intro y hy
  rw [srB_ioP_left]
  by_contra h
  simp only [decide_eq_false_iff_not, not_not] at h
  obtain ⟨owner, h⟩ := h
  obtain ⟨-, -, hb⟩ := hA y hy f l owner h
  have := hfree f.val le_rfl hfl
  rw [hb f.val le_rfl hfl] at this; cases this

theorem genObjRefs_ioP (f l : U64) :
    Fl4Spec.genObjRefs (absCap (.IoPort f l 0#u64)) =
      {Fl4Spec.GenObjRef.archRef (Fl4Spec.ArchGenObjRef.ioPortRef (BitVec.ofNat 16 f.val))} := by
  ext g
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archCapSetMap,
    Fl4Spec.archGenObjRefs, Fl4Spec.aobjRef]

/-- A cap overlapping an IO port cap is one, from the same first port. -/
theorem ovl_ioP {f l : U64} {c : capability.Cap} (h : Ovl (absCap (.IoPort f l 0#u64)) (absCap c)) :
    ∃ f' l' owner, c = .IoPort f' l' owner ∧ (BitVec.ofNat 16 f'.val : BitVec 16) = BitVec.ofNat 16 f.val := by
  unfold Ovl at h
  rw [genObjRefs_ioP, ← Set.nonempty_iff_ne_empty] at h
  obtain ⟨g, hg1, hg2⟩ := h
  rw [Set.mem_singleton_iff.1 hg1] at hg2
  cases c <;> simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt,
    Fl4Spec.archCapSetMap, Fl4Spec.archGenObjRefs, Fl4Spec.aobjRef] at hg2 ⊢
  exact hg2.symm

/-- **A new IO port cap over free ports overlaps no cap of the MDB.** -/
theorem ovl_fresh_io {mem : U64 → U64} {kb : U64} {G : MdbGhost} (hA : IoPortsAlloc mem kb G) {f l : U64}
    (hfl : f.val ≤ l.val) (hl : l.val < 65536)
    (hfree : ∀ p, f.val ≤ p → p ≤ l.val → bitOf mem kb p = false) :
    ∀ y ∈ G.chains.flatten, ¬ Ovl (absCap (.IoPort f l 0#u64)) (absCap (capV mem y)) := by
  intro y hy ho
  obtain ⟨f', l', owner, hc, he⟩ := ovl_ioP ho
  obtain ⟨h1, h2, hb⟩ := hA y hy f' l' owner hc
  have e : f'.val = f.val := by
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have := hfree f.val le_rfl hfl
  rw [← e, hb f'.val le_rfl h1] at this; cases this

theorem and_ffff (x : U64) : (x &&& 65535#u64).val = x.val % 65536 := by
  rw [UScalar.val_and]
  have : (65535#u64 : U64).val = 2 ^ 16 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem ucast16_toNat (x : U64) : (Fl4Spec.ucast 16 x.bv : BitVec 16).toNat = x.val % 65536 := by
  simp [Fl4Spec.ucast]

/-! ## The spec's range check -/

section
open Fl4Spec

theorem isIoportRangeFree_run (f l : IoPort) (σ : State Unit) :
    isIoportRangeFree (Z := Unit) f l σ =
      ({(decide ({x | f ≤ x ∧ x ≤ l} ∩ {x | σ.archState.x64AllocatedIoPorts x = true} = ∅), σ)}, False) := by
  unfold isIoportRangeFree
  rw [nd_bind_single (m := NonDet.gets fun s : State Unit => s.archState.x64AllocatedIoPorts) rfl]; rfl

theorem rangeFree_iff {mem : U64 → U64} {kb : U64} {σ : State Unit} (hI : IoRel mem kb σ) {f l : Nat}
    (hl : l < 65536) (hf : f < 65536) :
    ({x : IoPort | BitVec.ofNat 16 f ≤ x ∧ x ≤ BitVec.ofNat 16 l} ∩
      {x | σ.archState.x64AllocatedIoPorts x = true} = ∅) ↔
    ∀ p, f ≤ p → p ≤ l → bitOf mem kb p = false := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h p h1 h2
    have hp : p < 65536 := by omega
    have := h (BitVec.ofNat 16 p)
    rw [← hI p hp]
    by_contra hb
    apply this
    refine ⟨⟨?_, ?_⟩, by simpa using hb⟩
    · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hp]; exact h1
    · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hp]; exact h2
  · rintro h x ⟨⟨h1, h2⟩, h3⟩
    have hx : x.toNat < 65536 := x.isLt
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf] at h1
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl] at h2
    have e := hI x.toNat hx
    rw [show BitVec.ofNat 16 x.toNat = x by simp] at e
    have := h x.toNat h1 h2
    rw [← e] at this
    simp only [Set.mem_setOf_eq] at h3
    rw [h3] at this; cases this

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem FrameInv.of_same' {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G)
    (hF : Vs.FrameInv m G) (hS : SlotsSame th m m') : Vs.FrameInv m' G :=
  hF.of_caps (fun z hz => hS.capV ((hM.members z).1 hz).1)

/-- The outcome of an IOPortControl invocation against a spec decode `m`:
the same error with the state unchanged, or an invocation after which (with
`set_thread_state Restart` first) `arch_perform_invocation` has an outcome
in related states, with `FinInv` and `IoPortsAlloc`. -/
def IoCPost (th : TypedHeap) (kb : U64) (σ : Fl4Spec.State Unit) (m : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation)
    (s : S) : core.result.Result Unit error.Exc × S × A → Prop
  | (.Err e, s', _) => s' = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e'
  | (.Ok (), s', _) => ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      ∃ σ' G' r, (.ok r, σ') ∈ ((Fl4Spec.archPerformInvocation (Z := Unit) inv).run σ1).1 ∧
        CRel th (L.mem s') σ' G' ∧ IoRel (L.mem s') kb σ' ∧ FinInv th (L.mem s') σ' G' ∧
        IoPortsAlloc (L.mem s') kb G' ∧ MdbOKV kb (L.mem s') G'

theorem IoCPost.of_run {th : TypedHeap} {kb : U64} {σ : Fl4Spec.State Unit}
    {m m' : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation} (h : m.run σ = m'.run σ) {s : S}
    {res : core.result.Result Unit error.Exc × S × A} (hq : IoCPost (L := L) th kb σ m' s res) :
    IoCPost (L := L) th kb σ m s res := by
  obtain ⟨r, s', a'⟩ := res
  cases r with
  | Err e => obtain ⟨h1, e', h2, h3⟩ := hq; exact ⟨h1, e', h.trans h2, h3⟩
  | Ok u => obtain ⟨inv, h2, h3⟩ := hq; exact ⟨inv, h.trans h2, h3⟩

theorem IoCPost.congr {th : TypedHeap} {kb : U64} {σ : Fl4Spec.State Unit}
    {m m' : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation} (h : m.run σ = m'.run σ) {s : S}
    {prog : Result (core.result.Result Unit error.Exc × S × A)}
    (hp : prog ⦃ res => IoCPost (L := L) th kb σ m' s res ⦄) : prog ⦃ res => IoCPost (L := L) th kb σ m s res ⦄ :=
  WP.spec_mono hp (fun _ hq => IoCPost.of_run h hq)

theorem IoCPost.err {th : TypedHeap} {kb : U64} {σ : Fl4Spec.State Unit}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation} {s : S} {a : A} {e : error.Exc} {e' : Fl4Spec.SyscallError}
    (h : m.run σ = ({(.error e', σ)}, False)) (he : ErrRel e e') :
    (ok ((.Err e, s, a) : core.result.Result Unit error.Exc × S × A)) ⦃ res =>
      IoCPost (L := L) th kb σ m s res ⦄ := by
  rw [WP.spec_ok]; exact ⟨rfl, e', h, he⟩

/-- `target_tail` for `IoCPost`. -/
theorem io_target_tail (th : TypedHeap) (kb : U64)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s))
    (c : capability.Cap) (ac : Fl4Spec.Cap) (hca : CapRel c ac) (hcv : CapValid th c) (idx dep : U64)
    (ks : Fl4Spec.CslotPtr → Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation)
    (K : obj.Slot → Result (core.result.Result Unit error.Exc × S × A))
    (hK : ∀ dsl pd, dsl.1 = pd.bv → th pd = some (.cnode dsl.2.length) →
      capAt (L.mem s) (cslotAddr dsl) = ok .Null →
      K (cslotAddr dsl) ⦃ res => IoCPost (L := L) th kb σ (ks dsl) s res ⦄) :
    (do
      let r ← cspace.lookup_target_slot st s c idx dep
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r1 ← cdt.ensure_empty_slot st s val
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ => K val
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.Exc) residual
          ok (r2, s, ar)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.Exc) residual
        ok (r1, s, ar)) ⦃ res =>
      IoCPost (L := L) th kb σ (Fl4Spec.lookupTargetSlot ac (Fl4Spec.dataToCptr idx.bv) (Fl4Spec.unat dep.bv) >>=
        fun d => Fl4Spec.ensureEmpty d >>= fun _ => ks d) s res ⦄ := by
  unfold cspace.lookup_target_slot
  obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false c ac hca hcv idx dep)
  rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) ac (Fl4Spec.dataToCptr idx.bv) (Fl4Spec.unat dep.bv)).run σ =
      ({(e1, σ)}, False) := he1
  cases r1 with
  | Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
      exact IoCPost.err (run_bind_error hlt _) (Or.inl hrel1)
  | Ok dest =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd⟩ := hrel1
      obtain ⟨cd, ad, hcd, hcad, hgd⟩ := hR.slot_cap (Z := Unit) hpd1 hpd
      unfold cdt.ensure_empty_slot
      simp only [slot_cap_eq, hcd, bind_ok]
      have hee := ensureEmpty_run dsl σ hgd
      refine IoCPost.congr (run_bind_ok hlt _) ?_
      by_cases hdn : cd = .Null
      swap
      · rw [cap_is_null_ne hdn]
        simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.FromSame.from, bind_tc_ok]
        have : ad ≠ .nullCap := fun h => hdn ((hcad.null_iff).1 h)
        simp only [this, ↓reduceIte] at hee
        exact IoCPost.err (run_bind_error hee _) (Or.inl trivial)
      subst hdn
      have hadn : ad = .nullCap := (hcad.null_iff).2 rfl
      simp only [hadn, ↓reduceIte] at hee
      rw [cap_is_null_null]
      simp only [bind_ok, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch]
      refine IoCPost.congr (run_bind_ok hee _) ?_
      exact hK dsl pd hpd1 hpd hcd

theorem MaskPost.slotsSame {th : TypedHeap} (hP : Placed th) {kb : U64} (hL : IoLayout th kb) {s s' : S}
    {low high : U64} {set : Bool} (h : MaskPost (L := L) kb low high set s s') : SlotsSame th (L.mem s) (L.mem s') :=
  io_frame_slotsSame hP hL h.2.1

/-- **`set_thread_state Restart`, with the bitmap relation.** -/
theorem restart_io (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IoLayout th (L.ksb s)) (hIo : IoRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w) :
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s1 =>
      L.ksb s1 = L.ksb s ∧ SlotsSame th (L.mem s) (L.mem s1) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        CRel th (L.mem s1) σ1 G ∧ IoRel (L.mem s1) (L.ksb s) σ1 ∧
        ∀ w : U64, w.val < 1024 → L.mem s1 (ioA (L.ksb s) w) = L.mem s (ioA (L.ksb s) w) ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  refine WP.spec_mono (WP.spec_and (WP.spec_and (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact)
    (set_thread_state_ksb s ct sched.TS_RESTART)) (set_thread_state_cases s ct sched.TS_RESTART)) ?_
  rintro s1 ⟨⟨hS, hkb⟩, hcase⟩
  obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
  rw [← hcur] at hk
  obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, -, -⟩ := restart_rel hR hV hM hC hS hk .restart
  obtain ⟨-, -, ha1, -, -⟩ := setThreadState_keeps hk hst
  have hw : ∀ w : U64, w.val < 1024 → L.mem s1 (ioA (L.ksb s) w) = L.mem s (ioA (L.ksb s) w) := by
    intro w hwl
    have hsa : P1.Aligned (stA ct) := by
      unfold P1.Aligned; rw [stA_val hP htcb]; have := hP.align ct _ htcb; omega
    have hio := hL.out w hwl
    have hne : stA ct ≠ ioA (L.ksb s) w := by
      intro e
      have := hio.2 ct _ htcb
      have h2 := stA_val hP htcb
      rw [e] at h2
      simp [objSize] at this; omega
    rcases hcase with rfl | rfl
    · rw [L.mem_wr _ _ _ _ hsa hio.1, if_neg hne]
    · rw [L.mem_wr _ _ _ _ hact.1 hio.1, if_neg (hact3 w hwl), L.mem_wr _ _ _ _ hsa hio.1, if_neg hne]
  refine ⟨hkb, hS, σ1, hst, ⟨hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS⟩, fun p hp => ?_, hw⟩
  rw [ha1, hIo p hp]
  unfold bitOf
  rw [hw _ (by rw [wI_val hp]; omega)]

@[simp] theorem lbl_ioctl_val : fl4_abi.label.X86IOPortControlIssue.val = 63 := by
  simp [fl4_abi.label.X86IOPortControlIssue]

/-- **IOPortControl `Issue`** (label 63). -/
theorem ioport_control_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hL : IoLayout th (L.ksb s)) (hIo : IoRel (L.mem s) (L.ksb s) σ)
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl) (ac : Fl4Spec.ArchCap) :
    ioport.decode_control st arI s ar fl4_abi.label.X86IOPortControlIssue length (cslotAddr (ps.bv, idxs)) buf
      extra ⦃ res =>
      IoCPost (L := L) th (L.ksb s) σ
        (Fl4Spec.decodeIoportControlInvocation slbl (args.map UScalar.bv) (ps.bv, idxs) ac excaps) s res ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  unfold ioport.decode_control
  rw [if_neg (by simp)]
  unfold Fl4Spec.decodeIoportControlInvocation
  rw [if_pos hlbl]
  by_cases h4 : length < 4#u64
  · rw [if_pos h4]; simp only [error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 4 ∧ excaps.length ≥ 1) by simp; scalar_tac)]
    exact IoCPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) rfl (Or.inl trivial)
  rw [if_neg h4]
  rw [hx0]; simp only [bind_ok, is_null_eq]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, c0, ac0, erest, hc0, hca0, hcv0, rfl⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 4 ∧ ([] : List Fl4Spec.Cap).length ≥ 1) by simp)]
    exact IoCPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) rfl (Or.inl trivial)
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨y0, y1, y2, y3, rest, rfl⟩ : ∃ y0 y1 y2 y3 rest, args = y0 :: y1 :: y2 :: y3 :: rest := by
    match args with
    | [] | [_] | [_, _] | [_, _, _] => exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: y2 :: y3 :: rest => exact ⟨y0, y1, y2, y3, rest, rfl⟩
  rw [if_pos (show ((y0 :: y1 :: y2 :: y3 :: rest).map UScalar.bv).length ≥ 4 ∧ (ac0 :: erest).length ≥ 1 by simp)]
  simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), hargs 2#u64 y2 (by simp),
    hargs 3#u64 y3 (by simp), slot_cap_eq, hc0, lift, bind_ok]
  have hmap : List.map UScalar.bv (y0 :: y1 :: y2 :: y3 :: rest) = y0.bv :: y1.bv :: y2.bv :: y3.bv :: rest.map UScalar.bv :=
    rfl
  rw [hmap]
  have g0 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  have g1 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: rest.map UScalar.bv)[1]? = some y1.bv := rfl
  have g2 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: rest.map UScalar.bv)[2]? = some y2.bv := rfl
  have g3 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: rest.map UScalar.bv)[3]? = some y3.bv := rfl
  have ge : (ac0 :: erest)[0]? = some ac0 := rfl
  rw [g0, g1, g2, g3, ge]
  repeat rw [the_some]
  -- the ports
  have hf := and_ffff y0
  have hl := and_ffff y1
  have hf16 : (Fl4Spec.ucast 16 y0.bv : BitVec 16) = BitVec.ofNat 16 (y0 &&& 65535#u64).val := by
    apply BitVec.eq_of_toNat_eq; rw [ucast16_toNat, BitVec.toNat_ofNat, hf]; omega
  have hl16 : (Fl4Spec.ucast 16 y1.bv : BitVec 16) = BitVec.ofNat 16 (y1 &&& 65535#u64).val := by
    apply BitVec.eq_of_toNat_eq; rw [ucast16_toNat, BitVec.toNat_ofNat, hl]; omega
  rw [hf16, hl16]
  set first := y0 &&& 65535#u64 with hfirst
  set last := y1 &&& 65535#u64 with hlast
  have hfv : first.val < 65536 := by rw [hf]; omega
  have hlv : last.val < 65536 := by rw [hl]; omega
  by_cases hlt : last < first
  · rw [if_pos hlt]; simp only [error.invalid_arg, bind_ok]
    rw [whenE_pos (by rw [GT.gt, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfv,
      Nat.mod_eq_of_lt hlv]; scalar_tac)]
    exact IoCPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidArgument 1) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl rfl)
  rw [if_neg hlt]
  have hfl : first.val ≤ last.val := by scalar_tac
  rw [whenE_neg (by rw [GT.gt, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfv,
      Nat.mod_eq_of_lt hlv]; scalar_tac)]
  refine IoCPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the range must be free
  refine WP.spec_bind (range_free_eq s first last hfl hlv) ?_
  intro b hb
  refine IoCPost.congr (run_bind_ok (run_liftE (isIoportRangeFree_run _ _ σ)) _) ?_
  have hfree : decide ({x : Fl4Spec.IoPort | BitVec.ofNat 16 first.val ≤ x ∧ x ≤ BitVec.ofNat 16 last.val} ∩
      {x | σ.archState.x64AllocatedIoPorts x = true} = ∅) = b := by
    rw [hb]; exact decide_eq_decide.2 (rangeFree_iff hIo hlv hfv)
  rw [hfree]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [whenE_pos (by simp)]
    exact IoCPost.err (e := .Sys .RevokeFirst) (e' := .revokeFirst)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.revokeFirst :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl trivial)
  | true =>
  simp only [↓reduceIte]
  rw [whenE_neg (by simp)]
  refine IoCPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  have hfree' : ∀ p, first.val ≤ p → p ≤ last.val → bitOf (L.mem s) (L.ksb s) p = false := by
    simpa using hb.symm
  refine io_target_tail th (L.ksb s) s ar σ hR hV c0 ac0 hca0 hcv0 y2 y3 _ _ ?_
  intro dsl pd hpd1 hpd hdst
  obtain ⟨da, db⟩ := dsl
  simp only at hpd1 hpd; subst hpd1
  -- `set_thread_state Restart`
  refine WP.spec_bind (restart_io th hP s σ G ⟨hR, hV, hM, hC, hI⟩ hL hIo ct hcur htcb hact hact3) ?_
  rintro s2 ⟨hkb, hS, σ1, hst, hCR1, hIo1, hw⟩
  -- the bitmap
  have hL2 : IoLayout th (L.ksb s2) := by rw [hkb]; exact hL
  refine WP.spec_bind (set_mask_spec hL2 s2 rfl first last hfl hlv true) ?_
  intro s3 hM3
  have hS3 := MaskPost.slotsSame hP hL2 hM3
  have hIo3 : IoRel (L.mem s3) (L.ksb s) (ioMaskSt (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val) true σ1) := by
    rw [← hkb]; exact IoRel.mask (by rw [hkb]; exact hIo1) hlv hfl hM3
  set σ2 := ioMaskSt (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val) true σ1 with hσ2
  obtain ⟨hR2, hV2, hM2, hC2, hI2⟩ := crel_same hCR1 hS3 (σ' := σ2) rfl rfl rfl
  -- the insertion
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, db) := ⟨pd, rfl, Or.inl hpd⟩
  have hS23 := hS.trans hS3
  have hsrc3 : capAt (L.mem s3) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl := by rw [hS23.capAt hAs.isSlot, hsrcC]
  have hdst3 : capAt (L.mem s3) (cslotAddr (pd.bv, db)) = ok .Null := by rw [hS23.capAt hAd.isSlot, hdst]
  have hfr : ∀ y ∈ G.chains.flatten, srB (.IoPort first last 0#u64) (capV (L.mem s3) y) = false := by
    intro y hy
    rw [hS23.capV ((hM.members y).1 hy).1]
    exact io_fresh hPA hfl hfree' y hy
  have hFI2 : FinInv th (L.mem s3) σ2 G :=
    hFI.of_same hM hS23 ((ksub_of_eq (setThreadState_nks _ _) hst).trans (KSub.of_kheap rfl))
  have hov : ∀ y ∈ G.chains.flatten, ¬ Ovl (absCap (.IoPort first last 0#u64)) (absCap (capV (L.mem s3) y)) := by
    intro y hy
    rw [hS23.capV ((hM.members y).1 hy).1]
    exact ovl_fresh_io hPA hfl hlv hfree' y hy
  have hins := insert_ctl_full_fin th s3 σ2 G hR2 hV2 hP hM2 hC2 hI2 hFI2 hps hpd hls rfl hsrc3 hdst3
    (.IoPort first last 0#u64) ⟨hfv, hlv⟩ trivial ⟨hfv, hlv, canonical_zero⟩ trivial hfr hov
  have hnx : nextOf (L.mem s3) (cslotAddr (ps.bv, idxs)) = 0#u64 ∨
      IsSlot th (nextOf (L.mem s3) (cslotAddr (ps.bv, idxs))) := by
    have hsm : cslotAddr (ps.bv, idxs) ∈ G.chains.flatten := (hM2.members _).2 ⟨hAs.isSlot, _, hsrc3, by simp⟩
    rcases hM2.next_mem hsm with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ((hM2.members _).1 h).1
  have hfrm := insert_frame hP s3 (.IoPort first last 0#u64) _ _ hAs.isSlot hAd.isSlot _ hsrc3 hnx
  refine WP.spec_bind (WP.spec_and hins hfrm) ?_
  rintro s4 ⟨⟨σ', G', hci, hR', hV', hM', hC', hI', hFI', hcap4, ⟨bG, hGe⟩, hSt4⟩, hF4⟩
  rw [WP.spec_ok]
  have hkeep := capInsert_keeps (absCap (.IoPort first last 0#u64)) (ps.bv, idxs) (pd.bv, db) σ2 ((), σ')
    (by rw [hci]; rfl)
  have hIo4 : IoRel (L.mem s4) (L.ksb s) σ' := by
    intro p hp
    rw [hkeep.2.2, hIo3 p hp]
    unfold bitOf
    rw [hF4.out (hL.out _ (by rw [wI_val hp]; omega))]
  refine ⟨.invokeIOPortControl (.ioPortControlInvocation (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val)
    (pd.bv, db) (ps.bv, idxs)), rfl, σ1, hst, σ', G', [], ?_, ⟨hR', hV', hM', hC', hI'⟩, hIo4, hFI', ?_, ?_⟩
  · refine mem_liftE (x := ([], σ')) ?_
    refine mem_bind_nd (x := ((), σ')) ?_ rfl
    refine mem_bind_nd (x := ((), σ2)) (setIoportMask_mem _ _ _ _) ?_
    refine mem_bind_nd (x := (_, σ2)) rfl ?_
    show ((), σ') ∈ (Fl4Spec.capInsert (absCap (.IoPort first last 0#u64)) (ps.bv, idxs) (pd.bv, db) σ2).1
    rw [hci]; rfl
  · -- every IO port cap's ports are allocated: the new cap's now, the others' still
    have hal : ∀ p, p < 65536 → (bitOf (L.mem s) (L.ksb s) p = true ∨ (first.val ≤ p ∧ p ≤ last.val)) →
        bitOf (L.mem s4) (L.ksb s) p = true := by
      intro p hp hor
      rw [← hIo4 p hp, hkeep.2.2]
      simp only [hσ2, ioMaskSt]
      have e1 : (BitVec.ofNat 16 p ≥ BitVec.ofNat 16 first.val) ↔ first.val ≤ p := by
        rw [GE.ge, BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
          Nat.mod_eq_of_lt hfv]
      have e2 : (BitVec.ofNat 16 p ≤ BitVec.ofNat 16 last.val) ↔ p ≤ last.val := by
        rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hlv]
      by_cases hin : first.val ≤ p ∧ p ≤ last.val
      · rw [if_pos ⟨e1.2 hin.1, e2.2 hin.2⟩]
      · rw [if_neg (fun h => hin ⟨e1.1 h.1, e2.1 h.2⟩), hIo1 p hp]
        unfold bitOf
        rw [hw _ (by rw [wI_val hp]; omega)]
        exact (hor.resolve_right hin)
    intro y hy f l owner hc
    have hys := ((hM'.members y).1 hy).1
    rw [hcap4 y hys] at hc
    split_ifs at hc with hyd
    · cases hc
      exact ⟨hfl, hlv, fun p h1 h2 => hal p (by omega) (Or.inr ⟨h1, h2⟩)⟩
    · have hyn : capV (L.mem s3) y ≠ .Null := by rw [hc]; simp
      have hym : y ∈ G.chains.flatten := (hM2.members y).2 ⟨hys, _, capAt_capV _ _, hyn⟩
      rw [hS23.capV hys] at hc
      obtain ⟨h1, h2, hb⟩ := hPA y hym f l owner hc
      exact ⟨h1, h2, fun p hp1 hp2 => hal p (by omega) (Or.inl (hb p hp1 hp2))⟩

  · -- the MDB invariants: a fresh IO port cap, naming no memory
    exact (MdbStep.same_left hM hS23 hSt4).okv hFR

/-- **Any other IOPortControl label**: `IllegalOperation`. -/
theorem ioport_control_other (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64)
    (hl : lbl.val ≠ 63) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64IOPortControlIssue)
    (length slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ssl : Fl4Spec.CslotPtr) (ac : Fl4Spec.ArchCap) (excaps : List Fl4Spec.Cap) :
    ioport.decode_control st arI s ar lbl length slot buf extra ⦃ res =>
      IoCPost (L := L) th (L.ksb s) σ (Fl4Spec.decodeIoportControlInvocation slbl args ssl ac excaps) s res ⦄ := by
  unfold ioport.decode_control
  rw [if_pos (by rw [bne_iff_ne, ne_eq, u64_eq_iff]; simpa using hl)]
  simp only [error.illegal, bind_ok]
  unfold Fl4Spec.decodeIoportControlInvocation
  rw [if_neg hlbl]
  exact IoCPost.err (e := .Sys .IllegalOperation) (e' := .illegalOperation) rfl (Or.inl trivial)

end

end

end Fl4Proofs.P3
