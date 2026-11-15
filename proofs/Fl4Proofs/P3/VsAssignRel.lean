/-
P3 (DESIGN.md §9), VSpace: **ASIDPool `Assign` refines l4v** (decode, then
`set_thread_state cur Restart`, then `perform_asid_pool_invocation`).

`assign_rel`: FL4's `vspace::decode` on `AsidPool ptr base` with label
`X86ASIDPoolAssign` and a first extra cap `Pml4 ptr1` (unmapped) in a CNode
slot `sl`, either
* fails with an error related to the spec's decode error (`VsErrRel`), the
  states unchanged, or
* succeeds, and then the spec's decode has an outcome `assign asid ptr sl`
  (not failing), after which `set_thread_state cur Restart` and
  `perform_asid_pool_invocation` have the single outcome `σ'`, related again
  (CSpace `StateRel`/`SlotsValid`, `VsRel`, `SR`).

Hypotheses (`VsInvHyps`): the current thread (`curT`) and setting it
`Restart` (`restart`), from the scheduler relation; `SR` stable under the
slot write and the pool write (`capStable`, `vsStable`). The slots of the
typed heap are disjoint from the ASID table and pool words (`VsSlotsDisj`).
-/
import Fl4Proofs.P3.VsAssign
import Fl4Proofs.P3.VsFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- FL4's errors and the spec's, with the invalid-capability errors. -/
def VsErrRel (e : error.Exc) (e' : Fl4Spec.SyscallError) : Prop :=
  SysErrRel e e' ∨ ∃ n : U64, e = .Sys (.InvalidCapability n) ∧ e' = .invalidCapability n.val

/-- A spec change of one CNode slot. -/
def CapStep (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∃ p r cs idx a, σ.kheap p = some (.cnode r cs) ∧ σ' = setCnodeSlot σ p r cs idx a

/-- The cap-slot words of the typed heap. -/
def SlotW (th : TypedHeap) (b : U64) : Prop := ∃ x, IsSlot th x ∧ (b = x ∨ b = core.num.U64.wrapping_add x 8#u64)

/-- The slots are disjoint from the ASID table and the pools. -/
def VsSlotsDisj (th : TypedHeap) (P : Set U64) (ksb : U64) : Prop :=
  ∀ b, VsWrite P ksb b → ¬ SlotW th b

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

structure VsInvHyps (A : Type) (th : TypedHeap) (P : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  curT : ∀ s a σ, SR s a σ → sched.cur_thread st s ⦃ ct => ct.bv = σ.curThread ⦄
  restart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → SR s a σ → ct.bv = σ.curThread → σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    Fl4Spec.runnable x.tcbState = true →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄
  capStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (SlotW th) → CapStep σ σ' → SR s' a σ'
  vsStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (VsWrite P (L.ksb s)) → VsStep σ σ' → SR s' a σ'

end Hyps

section Spec
open Fl4Spec

theorem performAssign_eq {σ : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool}
    (hk : σ.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) {pb : ObjRef}
    {o : Option Asid} (hc : cs idx = some (.archObjectCap (.pml4Cap pb o))) {p : ObjRef}
    {f : AsidLowIndex → Option ObjRef} (hp : σ.kheap p = some (.archObj (.asidPool f))) (asid : Asid) :
    performAsidPoolInvocation (Z := Unit) (.assign asid p (pc, idx)) σ =
      ({((), updK (setCnodeSlot σ pc r cs idx (.archObjectCap (.pml4Cap pb (some asid)))) p
        (.archObj (.asidPool (Function.update f (asidLowBitsOf asid) (some pb)))))}, False) := by
  have hpc : p ≠ pc := kheap_ne hp hk (fun _ h1 h2 => by subst h1; cases h2)
  unfold performAsidPoolInvocation
  dsimp only
  rw [nd_bind_one (getCap_cnode hk hwf hc)]
  dsimp only
  rw [nd_bind_one (setCap_cnode _ hk hwf hidx)]
  unfold storeAsidPoolEntry
  have hp' : (setCnodeSlot σ pc r cs idx (.archObjectCap (.pml4Cap pb (some asid)))).kheap p =
      some (.archObj (.asidPool f)) := by simp [setCnodeSlot, hpc, hp]
  rw [nd_bind_one (getAsidPool_eq hp'), nd_pure_bind', setAsidPool_eq hp']

/-- The spec after the decode: `set_thread_state cur Restart`, then the
perform, with the single outcome `σ'`. -/
def AssignSpec (σ : State Unit) (asid ptr : ObjRef) (sl : CslotPtr) (σ' : State Unit) : Prop :=
  (setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
    performAsidPoolInvocation (.assign asid ptr sl)) σ = ({((), σ')}, False)

end Spec

/-- The relation only reads the table and pool words, the ASID table and the
pools' objects. -/
theorem VsRel.frame {P : Set U64} {m m' : U64 → U64} {ksb : U64} {σ σ' : Fl4Spec.State Unit} (hR : VsRel P m ksb σ)
    (hm : ∀ b, VsWrite P ksb b → m' b = m b) (ht : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hk : ∀ p ∈ P, σ'.kheap p.bv = σ.kheap p.bv) : VsRel P m' ksb σ' := by
  refine ⟨fun hi h => ?_, fun hi h h0 => ?_, fun p hp => ?_⟩
  · rw [ht, hm _ (Or.inl ⟨hi, h, rfl⟩)]; exact hR.table hi h
  · rw [hm _ (Or.inl ⟨hi, h, rfl⟩)] at h0 ⊢; exact hR.tmem hi h h0
  · obtain ⟨f, hf, hfe⟩ := hR.pool p hp
    exact ⟨f, (hk p hp).trans hf, fun lo h => by rw [hfe lo h, hm _ (Or.inr ⟨p, hp, lo, h, rfl⟩)]⟩

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A write to a word that is not a slot word keeps every slot's cap. -/
theorem capAt_wr_nonslot {th : TypedHeap} (hPl : Placed th) (s : S) {b : U64} (hb : Aligned b)
    (hns : ¬ SlotW th b) (v : U64) (x : U64) (hx : IsSlot th x) : capAt (L.mem (L.wr s b v)) x = capAt (L.mem s) x := by
  obtain ⟨p, i, hpi, rfl⟩ := hx
  unfold capAt
  rw [L.mem_wr_ne hb (hpi.al hPl) (fun h => hns ⟨_, ⟨p, i, hpi, rfl⟩, Or.inl (UScalar.eq_of_val_eq h)⟩),
    L.mem_wr_ne hb (hpi.al8 hPl) (fun h => hns ⟨_, ⟨p, i, hpi, rfl⟩, Or.inr (UScalar.eq_of_val_eq h)⟩)]

theorem SlotsValid.of_caps {th : TypedHeap} {mem mem' : U64 → U64} (hV : SlotsValid th mem)
    (hcap : ∀ x, IsSlot th x → capAt mem' x = capAt mem x) : SlotsValid th mem' := by
  refine ⟨fun p r hp i hi c hc => ?_, fun t ht i hi c hc => ?_⟩
  · rw [hcap _ ⟨p, i, Or.inl ⟨r, hp, hi⟩, rfl⟩] at hc; exact hV.cnode p r hp i hi c hc
  · rw [hcap _ ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩] at hc; exact hV.tcb t ht i hi c hc


theorem VsWrite.aligned {P : Set U64} {ksb b : U64} (hP : VsPlaced P ksb) (h : VsWrite P ksb b) : Aligned b := by
  rcases h with ⟨hi, hh, rfl⟩ | ⟨p, hp, lo, hl, rfl⟩
  · show _ % 8 = 0; rw [atA_val hP.ksb_fit hh]; have := hP.ksb_al; omega
  · obtain ⟨pa, pf⟩ := hP.pal p hp
    show _ % 8 = 0; rw [peA_val pf hl]; omega

/-- A word that is not a slot word is not either word of a slot. -/
theorem ne_slot_words {th : TypedHeap} (hPl : Placed th) {p : U64} {i : Nat} (h : IsSlotAt th p i) {b : U64}
    (hb : ¬ SlotW th b) : b.val ≠ (slotOf p i).val ∧ b.val ≠ (slotOf p i).val + 8 := by
  refine ⟨fun e => hb ⟨_, ⟨p, i, h, rfl⟩, Or.inl (UScalar.eq_of_val_eq e)⟩, fun e => hb ⟨_, ⟨p, i, h, rfl⟩, Or.inr ?_⟩⟩
  apply UScalar.eq_of_val_eq
  have := h.fit hPl
  rw [e, wa8_val (by omega)]

/-- The CSpace relation does not see heap objects other than CNodes and TCBs. -/
theorem StateRel.upd_other {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Unit} (hR : StateRel th mem σ)
    {q : U64} {ao : Fl4Spec.ArchKernelObj} (hq : σ.kheap q.bv = some (.archObj ao)) (o : Fl4Spec.KernelObject) :
    StateRel th mem (updK σ q.bv o) := by
  refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
  · obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode p r hp
    have : p.bv ≠ q.bv := kheap_ne hk hq (fun _ h1 h2 => by subst h1; cases h2)
    exact ⟨cs, by simp [this, hk], hwf, hs⟩
  · obtain ⟨x, hk, hs⟩ := hR.tcb t ht
    have : t.bv ≠ q.bv := kheap_ne hk hq (fun _ h1 h2 => by subst h1; cases h2)
    exact ⟨x, by simp [this, hk], hs⟩

theorem optRef_inj {a b : U64} (h : optRef a = optRef b) : a = b := by
  unfold optRef at h
  split_ifs at h with h1 h2 h2 <;>
    first
    | (rw [h1, h2])
    | (injection h with h; exact P1.eq_of_bv h)
    | (exact absurd h (by simp))

/-- Two states with the ASID relation, the same ASID table and pools: the
same table and pool words. -/
theorem VsRel.words_eq {P : Set U64} {m m' : U64 → U64} {ksb : U64} {σ σ' : Fl4Spec.State Unit}
    (hR : VsRel P m ksb σ) (hR' : VsRel P m' ksb σ')
    (ht : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) (hk : ∀ p ∈ P, σ'.kheap p.bv = σ.kheap p.bv) :
    ∀ b, VsWrite P ksb b → m' b = m b := by
  rintro b (⟨hi, h, rfl⟩ | ⟨p, hp, lo, hl, rfl⟩)
  · exact optRef_inj ((hR'.table hi h).symm.trans (by rw [ht]; exact hR.table hi h))
  · obtain ⟨f, hf, hfe⟩ := hR.pool p hp
    obtain ⟨f', hf', hfe'⟩ := hR'.pool p hp
    rw [hk p hp, hf] at hf'
    injection hf' with hf'; injection hf' with hf'; injection hf' with hf'; subst hf'
    exact optRef_inj ((hfe' lo hl).symm.trans (hfe lo hl))

/-- **ASIDPool `Assign`** (see the module docstring). -/
theorem assign_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsInvHyps st A th P SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s))
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hS : SR s a σ) {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (ptr base : U64) (hb : base.val % 512 = 0) (hb20 : base.val < 2 ^ 20)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr)
    (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length : U64) (slot : obj.Slot) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hex : vspace.extra ex 0#usize = ok (some (cslotAddr (pc.bv, idx))))
    {ptr1 asid0 : U64} (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pml4 ptr1 false asid0))
    (hcan : Canonical ptr1) (hp10 : ptr1 ≠ 0#u64)
    (htcb : ∀ ct : U64, ct.bv = σ.curThread → th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) :
    vspace.decode st ar s a fl4_abi.label.X86ASIDPoolAssign length slot (.AsidPool ptr base) call buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs cte (.asidPoolCap ptr.bv base.bv)
          ((.archObjectCap (.pml4Cap ptr1.bv none), (pc.bv, idx)) :: rest)) σ = ({(.error e', σ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧
        ¬ (ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs cte (.asidPoolCap ptr.bv base.bv)
          ((.archObjectCap (.pml4Cap ptr1.bv none), (pc.bv, idx)) :: rest)) σ).2 ∧
        ∃ asid σ', (.ok (.invokeASIDPool (.assign asid ptr.bv (pc.bv, idx))), σ) ∈
          (ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs cte (.asidPoolCap ptr.bv base.bv)
            ((.archObjectCap (.pml4Cap ptr1.bv none), (pc.bv, idx)) :: rest)) σ).1 ∧
          AssignSpec σ asid ptr.bv (pc.bv, idx) σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
          VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
          SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
          VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (.Pml4 ptr1 false asid0) ∧ KFoot σ σ' ∧
          ∀ b, VsWrite P (L.ksb s) b → L.mem res.2.1 b ≠ L.mem s b → L.mem res.2.1 b = ptr1) ⦄ := by
  rw [decodeAssign_eq hl args xs cte ptr.bv base.bv ptr1.bv (pc.bv, idx) rest]
  generalize hdec : ExceptT.run (assignBody ptr.bv base.bv (pc.bv, idx)) σ = dec
  unfold vspace.decode
  refine WP.spec_bind (hH.curT s a σ hS) ?_
  rintro ct hct
  have hlb : (fl4_abi.label.X86ASIDPoolAssign != fl4_abi.label.X86ASIDPoolAssign) = false := by simp
  simp only [hlb, Bool.false_eq_true, ↓reduceIte]
  rw [hex]
  apply ok_bind_spec
  dsimp only
  rw [slot_cap_eq, hcx]
  apply ok_bind_spec
  dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- the slot of the PML4 cap
  have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
  have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
  have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) := ⟨pc, _, hxs, hx0⟩
  obtain ⟨cs, hkc, hwf, hsl⟩ := hSt.cnode pc r hpc
  have hcs : cs idx = some (.archObjectCap (.pml4Cap ptr1.bv none)) := by
    obtain ⟨c, ac, hc, hac, hca⟩ := hsl idx hidx
    have : c = .Pml4 ptr1 false asid0 := by
      have h2 : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok c := hc
      rw [hcx] at h2; exact (by simpa using h2 : capability.Cap.Pml4 ptr1 false asid0 = c).symm
    subst this
    rw [hac, ← hca.2]; rfl
  have hL : vspace.ASID_LOW_BITS = 9#u64 := by unfold vspace.ASID_LOW_BITS; rfl
  rw [hL]
  step as ⟨i, hi⟩
  refine WP.spec_bind (asid_table_spec s i) ?_
  rintro w rfl
  have hiv : i.val = base.val >>> 9 := by simpa using hi
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have htab := hR.table _ hlt
  rw [hi_bv base i hiv] at htab
  by_cases hp : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = 0#u64
  · simp only [hp, ↓reduceIte]
    refine (WP.spec_ok _).2 ?_
    rw [hp, optRef_zero] at htab
    refine Or.inl ⟨_, .failedLookup false .invalidRoot, rfl,
      Or.inl (show SysErrRel _ (.failedLookup false .invalidRoot) from ⟨rfl, trivial⟩), ?_, rfl, rfl⟩
    rw [← hdec]; exact assignBody_noPool htab
  · simp only [hp, ↓reduceIte]
    rw [optRef, if_neg hp] at htab
    by_cases hwp : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = ptr
    · have hne : (L.mem s (atA (L.ksb s) (i &&& 2047#u64)) != ptr) = false := by simp [hwp]
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      rw [hwp] at htab ⊢
      have hpP : ptr ∈ P := hwp ▸ hR.tmem _ hlt hp
      obtain ⟨f, hkf, -⟩ := hR.pool ptr hpP
      have hpf := (hVP.pal ptr hpP).2
      refine WP.spec_bind (decode_loop1_spec s base ptr hpf) ?_
      rintro i1 ⟨hi1le, hall, hfound⟩
      by_cases h512 : i1 = 512#u64
      · simp only [h512, ↓reduceIte]
        refine (WP.spec_ok _).2 ?_
        refine Or.inl ⟨_, .deleteFirst, rfl, Or.inl (show SysErrRel _ .deleteFirst from trivial), ?_, rfl, rfl⟩
        rw [← hdec]
        refine assignBody_full htab hkf (full_of_none hR hpP hkf base fun j hj => hall j ?_)
        rw [h512]; exact hj
      · simp only [h512, ↓reduceIte]
        have hi1 : i1.val < 512 := by
          have : i1.val ≠ 512 := fun h => h512 (UScalar.eq_of_val_eq h)
          omega
        obtain ⟨h0, he⟩ := hfound hi1
        set asid := core.num.U64.wrapping_add base i1 with hasid
        have hoff := free_of_found hR hpP hkf base i1 hi1 h0 he
        obtain ⟨hmem, hnf⟩ := assignBody_mem (sl := (pc.bv, idx)) htab hkf hoff
        rw [ucast64_ucast9 i1 hi1 base] at hmem
        unfold lift
        apply ok_bind_spec
        -- `Restart`
        have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hct]; exact hkt
        refine WP.spec_bind (WP.spec_and (hH.restart s a σ ct xct hSt hSV hR hS hct hkt' (htcb ct hct) hact hrun)
          (set_thread_state_slots th hPl s ct sched.TS_RESTART (htcb ct hct) hact)) ?_
        rintro s1 ⟨⟨hSt1, hSV1, hR1, hS1, hk1⟩, hSS1⟩
        set σ1 := stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv with hσ1
        have hpct : pc.bv ≠ ct.bv := kheap_ne hkc hkt' (fun _ h1 h2 => by subst h1; cases h2)
        have hptct : ptr.bv ≠ ct.bv := kheap_ne hkf hkt' (fun _ h1 h2 => by subst h1; cases h2)
        have hkc1 : σ1.kheap pc.bv = some (.cnode r cs) := by rw [hσ1, stsAct_kheap]; simp [hpct, hkc]
        have hkf1 : σ1.kheap ptr.bv = some (.archObj (.asidPool f)) := by rw [hσ1, stsAct_kheap]; simp [hptct, hkf]
        -- the cap
        set nc : Fl4Spec.Cap := .archObjectCap (.pml4Cap ptr1.bv (some asid.bv))
        have hca : CapRel (.Pml4 ptr1 true asid) nc := ⟨trivial, rfl⟩
        refine WP.spec_bind (WP.spec_and (set_cap_refines th s1 σ1 hSt1 hSV1 hPl hpc hidx _ _ hca trivial hcan)
          (WP.spec_and (set_cap_spec (L := L) _ s1 (.Pml4 ptr1 true asid)) (set_cap_foot hPl hxsl s1 (.Pml4 ptr1 true asid) hcan))) ?_
        rintro s2 ⟨⟨σ2, hsc, hSt2, hSV2, -, -, -, hfr2⟩, hs2, hF2, hcv2⟩
        have hσ2 : σ2 = setCnodeSlot σ1 pc.bv r cs idx nc := by
          rw [setCap_cnode nc hkc1 hwf hidx] at hsc
          have := congrArg Prod.fst hsc
          simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
          exact this.symm
        subst hσ2
        set σ2 := setCnodeSlot σ1 pc.bv r cs idx nc with hσ2
        have hks2 : L.ksb s2 = L.ksb s := by rw [hs2]; simp [hk1]
        -- the frame of the slot write
        have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s2 b = L.mem s1 b := by
          intro b hb
          obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
          exact hfr2 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        have hpools : ∀ q ∈ P, σ2.kheap q.bv = σ1.kheap q.bv := by
          intro q hq
          obtain ⟨g, hg, -⟩ := hR1.pool q hq
          have : q.bv ≠ pc.bv := kheap_ne hg hkc1 (fun _ h1 h2 => by subst h1; cases h2)
          simp [hσ2, setCnodeSlot, this]
        have hR2 : VsRel P (L.mem s2) (L.ksb s2) σ2 := by
          rw [hks2]; rw [hk1] at hR1
          exact hR1.frame hfrV rfl hpools
        have hWs : WritesIn st s1 s2 (SlotW th) := by
          refine ⟨by rw [hs2]; simp, by rw [hs2]; simp, fun b hb hn => ?_⟩
          obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
          exact hfr2 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        have hS2 := hH.capStable _ _ a _ σ2 hS1 hWs ⟨pc.bv, r, cs, idx, nc, hkc1, rfl⟩
        have hkf2 : σ2.kheap ptr.bv = some (.archObj (.asidPool f)) := (hpools ptr hpP).trans hkf1
        -- the pool write
        apply ok_bind_spec
        have hlo := and_lt asid 9 511#u64 rfl (by decide)
        step as ⟨i3, hi3⟩
        have hval : (asid &&& 511#u64).val = asid.val &&& 511 := by simp [UScalar.val_and]
        have he4 : core.num.U64.wrapping_add ptr i3 = peA ptr (asid &&& 511#u64) := by
          apply UScalar.eq_of_val_eq
          rw [peA_val hpf hlo]
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hi3]; omega
        rw [he4, L.write_eq]
        apply ok_bind_spec
        set σ3 := updK σ2 ptr.bv (.archObj (.asidPool
          (Function.update f (Fl4Spec.asidLowBitsOf asid.bv) (some ptr1.bv)))) with hσ3
        have hpeW0 : VsWrite P (L.ksb s) (peA ptr (asid &&& 511#u64)) := Or.inr ⟨ptr, hpP, _, hlo, rfl⟩
        have hbo : OutsideObjects th (peA ptr (asid &&& 511#u64)) := hVO _ hpeW0
        have hFt : SlotFoot th (L.mem s) (L.mem (L.wr s2 (peA ptr (asid &&& 511#u64)) ptr1)) (cslotAddr (pc.bv, idx)) :=
          (SlotFoot.of_same hSS1 _).trans (hF2.trans (SlotFoot.wr_out hPl s2 hbo _))
        have hLk : VsLike (capV (L.mem (L.wr s2 (peA ptr (asid &&& 511#u64)) ptr1)) (cslotAddr (pc.bv, idx)))
            (.Pml4 ptr1 false asid0) := by
          rw [capV_wr_out hPl hxsl s2 hbo, hcv2]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by
            simp only [VCapOK] at h ⊢
            refine ⟨h.1, h.2.1, fun _ => ⟨h0, ?_⟩⟩
            have : asid.val = base.val + i1.val := by
              rw [hasid]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
            rw [this]; omega⟩
        have hKf : KFoot σ σ3 := (KFoot.sts hkt' _).trans ((KFoot.cnode hkc1 hwf idx nc).trans (KFoot.arch hkf2 _))
        refine (WP.spec_ok _).2 (Or.inr ⟨rfl, by rw [← hdec]; exact hnf, asid.bv, σ3, by rw [← hdec]; exact hmem,
          ?_, ?_, ?_, ?_, ?_, hFt, hLk, hKf, ?_⟩)
        · unfold AssignSpec
          rw [← hct, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
          exact performAssign_eq hkc1 hwf hidx hcs hkf1 asid.bv
        all_goals
          have hpeW : VsWrite P (L.ksb s) (peA ptr (asid &&& 511#u64)) := Or.inr ⟨ptr, hpP, _, hlo, rfl⟩
          have hpeA : Aligned (peA ptr (asid &&& 511#u64)) := hpeW.aligned hVP
          have hcaps := capAt_wr_nonslot (L := L) hPl s2 hpeA (hD _ hpeW) ptr1
        · exact Vs.StateRel.upd_other (hSt2.of_caps hcaps) hkf2 _
        · exact Vs.SlotsValid.of_caps hSV2 hcaps
        · show VsRel P (L.mem (L.wr s2 (peA ptr (asid &&& 511#u64)) ptr1))
            (L.ksb (L.wr s2 (peA ptr (asid &&& 511#u64)) ptr1)) σ3
          have := hR2.upd_entry (hks2 ▸ hVP) hpP hkf2 hlo ptr1
            (fun b hb hne => L.mem_wr_ne hpeA hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hpeA)
          rw [lo_bv, show optRef ptr1 = some ptr1.bv by unfold optRef; rw [if_neg hp10]] at this
          rw [LawfulStore.ksb_wr]
          exact this
        · refine hH.vsStable s2 _ a σ2 σ3 hS2 ⟨by simp, by simp, fun b hb hn => L.mem_wr_ne hpeA hb fun h => hn ?_⟩
            (Or.inl ⟨ptr.bv, f, _, hkf2, rfl⟩)
          rw [hks2, show b = peA ptr (asid &&& 511#u64) from (UScalar.eq_of_val_eq h).symm]
          exact hpeW
        · intro b hb hne
          by_cases e : peA ptr (asid &&& 511#u64) = b
          · subst e; exact L.mem_wr_same hpeA
          · have hba := hb.aligned hVP
            rw [L.mem_wr_ne hpeA hba (fun h => e (UScalar.eq_of_val_eq h)), hfrV b hb] at hne ⊢
            refine absurd ?_ hne
            have hpools1 : ∀ q ∈ P, σ1.kheap q.bv = σ.kheap q.bv := by
              intro q hq
              obtain ⟨g, hg, -⟩ := hR.pool q hq
              have : q.bv ≠ ct.bv := kheap_ne hg hkt' (fun _ h1 h2 => by subst h1; cases h2)
              rw [hσ1, stsAct_kheap]; simp [this]
            have ht1 : σ1.archState.x64AsidTable = σ.archState.x64AsidTable := by
              rw [hσ1]; unfold stsAct; split_ifs <;> rfl
            rw [hk1] at hR1
            exact hR.words_eq hR1 ht1 hpools1 b hb
    · have hne : (L.mem s (atA (L.ksb s) (i &&& 2047#u64)) != ptr) = true := by simp [hwp]
      simp only [hne, ↓reduceIte]
      rw [show error.invalid_cap Unit 0#u64 = ok (.Err (.Sys (.InvalidCapability 0#u64))) from rfl]
      apply ok_bind_spec
      refine (WP.spec_ok _).2 ?_
      refine Or.inl ⟨_, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩, ?_, rfl, rfl⟩
      rw [← hdec]
      exact assignBody_wrong htab (fun h => hwp (eq_of_bv h).symm)

end

end

end Fl4Proofs.P3.Vs
