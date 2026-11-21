/-
P3 (DESIGN.md §9), VSpace: **PageDirectory `Map` refines l4v**
(`decode_page_directory_invocation`, `Restart`,
`perform_page_directory_invocation`): VsPtMapRel one level up. FL4's
`vspace::decode_table` at level 30 writes a PDPT entry built by
`make_user_table`; l4v stores a `PageDirectoryPDPTE`. Hypotheses
(`VsPdMapHyps`) as for the page-table map, with `SR` stable under PDPT-entry
writes.
-/
import Fl4Proofs.P3.VsPdMap
import Fl4Proofs.P3.VsFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- The entry words of the PDPTs of `L3`. -/
def PdptW (L3 : Set U64) (b : U64) : Prop := ∃ p ∈ L3, ∃ i : U64, i.val < 512 ∧ b = peA p i

/-- The spec change of a PDPTE write. -/
def PdptStep (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∃ p f f', σ.kheap p = some (.archObj (.pdPointerTable f)) ∧ σ' = updK σ p (.archObj (.pdPointerTable f'))

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The hypotheses of the page-directory map (see the module docstring). -/
structure VsPdMapHyps (A : Type) (ar : machine.Arch A) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  restart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → SR s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    Fl4Spec.runnable x.tcbState = true →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄
  capStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (SlotW th) → CapStep σ σ' → SR s' a σ'
  pdptStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PdptW L3) → PdptStep σ σ' → SR s' a σ'
  flushOK : ∀ (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid) (σ : Fl4Spec.State Unit),
    ¬ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid σ).2
  flushPS : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid : U64), SR s a σ → ar.invalidate_page_structures a asid ⦃ a' =>
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧ SR s a' σ' ⦄

end Hyps
/-- **The relation after writing entry `i` of the PDPT at `p`.** -/
theorem PtRel.upd_l3 {L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {σ : Fl4Spec.State Unit} (hP : PtPlaced L4 L3 L2 L1)
    (hR : PtRel L4 L3 L2 L1 m σ) {p : U64} (hp : p ∈ L3) {f : BitVec 9 → Fl4Spec.PDPTE}
    (hk : σ.kheap p.bv = some (.archObj (.pdPointerTable f))) {i : U64} (hi : i.val < 512) (v : U64)
    (pde : Fl4Spec.PDPTE) (hv : PDPTERel L2 v pde) (hm : ∀ b, Aligned b → b ≠ peA p i → m' b = m b)
    (hme : m' (peA p i) = v) :
    PtRel L4 L3 L2 L1 m' (updK σ p.bv (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 i.bv) pde)))) := by
  have hpa := hP p (Or.inr (Or.inl hp))
  have hal : ∀ q j : U64, q.val % 4096 = 0 → j.val < 512 → Aligned (peA q j) := fun q j hq hj => by
    show _ % 8 = 0; rw [peA_val (tbl_fit hq) hj]; omega
  have hoth : ∀ q j : U64, q.val % 4096 = 0 → q ≠ p → j.val < 512 → m' (peA q j) = m (peA q j) :=
    fun q j hq hqp hj => hm _ (hal q j hq hj) (peA_ne hq hpa hqp hj hi)
  have hkq : ∀ q : U64, ∀ o, σ.kheap q.bv = some o → (∀ g, o ≠ .archObj (.pdPointerTable g)) →
      (updK σ p.bv (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 i.bv) pde)))).kheap q.bv = some o ∧
        q ≠ p := by
    intro q o hq hno
    have hqp : q ≠ p := fun e => by subst e; rw [hk] at hq; injection hq with hq; exact hno f hq.symm
    exact ⟨by simp [updK, show q.bv ≠ p.bv from fun h => hqp (eq_of_bv h), hq], hqp⟩
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l4 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inl hq)
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp (by omega)]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l3 q hq
    have hqa := hP q (Or.inr (Or.inl hq))
    by_cases e : q = p
    · subst e
      rw [hk] at hg; injection hg with hg; injection hg with hg; injection hg with hg; subst hg
      refine ⟨Function.update f (Fl4Spec.ucast 9 i.bv) pde, by simp [updK], fun j hj => ?_⟩
      by_cases ej : j = i
      · subst ej; rw [Function.update_self, hme]; exact hv
      · rw [Function.update_of_ne (fun h => ej (ucast_inj 9 hj hi h)),
          hm _ (hal q j hqa hj) (fun h => ej (by
            have := congrArg UScalar.val h
            rw [peA_val (tbl_fit hqa) hj, peA_val (tbl_fit hqa) hi] at this
            exact UScalar.eq_of_val_eq (by omega)))]
        exact hgf j hj
    · exact ⟨g, by simp [updK, show q.bv ≠ p.bv from fun h => e (eq_of_bv h), hg],
        fun j hj => by rw [hoth q j hqa e hj]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l2 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inr (Or.inr (Or.inl hq)))
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp hj]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l1 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inr (Or.inr (Or.inr hq)))
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp hj]; exact hgf j hj⟩

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The PDPTE FL4 builds for a page directory at `ptr` is l4v's `PageDirectoryPDPTE`. -/
theorem pdpte_of_make {ptr e : U64} {pwt pcd : Bool} {L2 : Set U64} (hp : ptr ∈ L2)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (he : e.bv = ((core.num.U64.wrapping_sub ptr layout.PPTR_BASE).bv &&& 4503599627366400#64) ||| tblLow pwt pcd)
    (ta : Fl4Spec.TableAttrs) (tr : Fl4Spec.CapRights) :
    PDPTERel L2 e (.pageDirectoryPDPTE (Fl4Spec.addrFromPPtr ptr.bv) ta tr) := by
  obtain ⟨b0, b7, bm⟩ := tblLow_bits pwt pcd
  have hbit : ∀ k, k < 12 → e.bv.getLsbD k = (tblLow pwt pcd).getLsbD k := by
    intro k hk; rw [he, or_bit, addr_lowbit _ _ hk]; simp
  have hA : eA e = core.num.U64.wrapping_sub ptr layout.PPTR_BASE := by
    apply eq_of_bv
    show (e &&& 4503599627366400#u64).bv = _
    have hM : (4503599627366400#u64 : U64).bv = 4503599627366400#64 := rfl
    rw [← hpa]
    simp only [UScalar.bv_and, he, hM, BitVec.and_or_distrib_right, bm, BitVec.and_assoc, BitVec.and_self]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (e &&& 1#u64) ≠ 0#u64
    have := and_ne0 e 0 (by decide) 1#u64 (by decide)
    rw [hbit 0 (by decide), b0] at this
    intro h; rw [h] at this; exact absurd this (by decide)
  · show ¬ (e &&& 128#u64) ≠ 0#u64
    have := and_ne0 e 7 (by decide) 128#u64 (by decide)
    rw [hbit 7 (by decide), b7] at this
    intro h; exact h (by simpa using this)
  · rw [hA, paddr_bv]
  · have : eT e = ptr := by
      unfold eT
      rw [hA]
      apply eq_of_bv
      rw [core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_sub_bv_eq]
      unfold layout.PPTR_BASE
      exact BitVec.sub_add_cancel _ _
    rw [this]; exact hp

theorem shl30 : (1#u64 <<< (30#u64 &&& 63#u64)) = ok 1073741824#u64 := by
  rw [and63_of_lt (by decide), shl_u64_eq _ _ (by decide)]; rfl

theorem vaddr30_bv (a0 : U64) :
    (a0 &&& ~~~(core.num.U64.wrapping_sub 1073741824#u64 1#u64)).bv = a0.bv &&& ~~~Fl4Spec.mask Fl4Spec.pdptShiftBits := by
  rw [UScalar.bv_and]
  congr 1

/-- `table_entry_slot` at level 30 is `lookup_pdpt_slot`. -/
theorem table_entry_slot_30 {L4 L3 L2 L1 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64)
    (hv : UserV vaddr) :
    vspace.table_entry_slot st s pm vaddr 30#u64 ⦃ r =>
      (∀ x, r = .Ok x → ExceptT.run (Fl4Spec.lookupPdptSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(.ok x.bv, σ)}, False) ∧
        ∃ q ∈ L3, x = peA q (vIdx vaddr 30)) ∧
      (∀ e, r = .Err e → ∃ n, e = .Sys (.FailedLookup false (.MissingCapability n)) ∧
        ExceptT.run (Fl4Spec.lookupPdptSlot (Z := Unit) pm.bv vaddr.bv) σ =
          ({(.error (.missingCapability n.val), σ)}, False)) ⦄ := by
  unfold vspace.table_entry_slot
  simp only [↓reduceIte]
  refine WP.spec_bind (lookup_pdpt_slot_rel s σ hR hP hpm vaddr hv) ?_
  rintro r ⟨hsp, hsl, hse⟩
  cases r with
  | Ok x =>
    exact (WP.spec_ok _).2 ⟨(fun y hy => by cases hy; exact ⟨hsp, hsl _ rfl⟩), fun e he => by cases he⟩
  | Err lf =>
    obtain ⟨n, rfl⟩ := hse _ rfl
    exact (WP.spec_ok _).2 ⟨(fun y hy => by cases hy), fun e he => by cases he; exact ⟨n, rfl, hsp⟩⟩

/-- `check_vspace` on a mapped PML4 cap, for the page-directory map. -/
theorem check_vspace_pml4_pd {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (p asid : U64) (h0 : asid ≠ 0#u64) (pp : Fl4Spec.ObjRef) (v at' : Fl4Spec.Data) (cte : Fl4Spec.CslotPtr)
    (hv : ¬ Fl4Spec.userVtop < v) :
    vspace.check_vspace st s (.Pml4 p true asid) ⦃ r =>
      (r = .Ok (p, asid) ∧
        ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False)) ∨
      (∃ e e', r = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (pdTail pp p.bv asid.bv v at' cte) σ = ({(.error e', σ)}, False)) ⦄ := by
  unfold vspace.check_vspace
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR asid h0) (find_vspace_for_asid_err s asid)) ?_
  rintro r ⟨hf, he⟩
  cases r with
  | Ok r1 =>
    by_cases hr : r1 = p
    · subst hr
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 (Or.inl ⟨rfl, hf⟩)
    · have : (r1 != p) = true := by simp [hr]
      simp only [this, ↓reduceIte, error.invalid_cap]
      exact (WP.spec_ok _).2 (Or.inr ⟨_, _, rfl, Or.inr ⟨1#u64, rfl, rfl⟩,
        pdTail_wrongVs hv hf (fun h => hr (eq_of_bv h))⟩)
  | Err lf =>
    obtain rfl := he lf rfl
    refine (WP.spec_ok _).2 (Or.inr ⟨_, _, rfl, Or.inl (show SysErrRel (.Sys (.FailedLookup false .InvalidRoot))
      (.failedLookup false .invalidRoot) by simp [SysErrRel, LookupFaultRel]), pdTail_noVs hv hf⟩)

/-- **PageDirectory `Map` refines l4v** (see the module docstring). -/
theorem pd_map_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPdMapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PdptW L3 b → ¬ VsWrite P (L.ksb s) b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool) (hpL2 : ptr ∈ L2) (hfe : EncWf (.PageDirectory ptr mp asid0 va0))
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_table st ar s a fl4_abi.label.X86PageDirectoryMap length (cslotAddr (pc.bv, idx))
      (.PageDirectory ptr mp asid0 va0) buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) xs (pc.bv, idx)
          (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) ((vc', xsl) :: rest)) σ =
            ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) xs
          (pc.bv, idx) (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) ((vc', xsl) :: rest)) σ =
            ({(.ok iv, σ)}, False) ∧
        PdMapSpec σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (.PageDirectory ptr mp asid0 va0) ∧ KFoot σ σ') ⦄ := by
  rw [show ∀ args' ex', Fl4Spec.archDecodeInvocation (Z := Unit) slbl args' xs (pc.bv, idx)
      (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) ex' =
    Fl4Spec.decodePageDirectoryInvocation slbl args' (pc.bv, idx)
      (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) ex' from fun _ _ => rfl]
  generalize hDec : ExceptT.run (Fl4Spec.decodePageDirectoryInvocation slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) ((vc', xsl) :: rest)) σ = D
  unfold vspace.decode_table
  have hne : ¬ fl4_abi.label.X86PageDirectoryMap = fl4_abi.label.X86PageDirectoryUnmap := by
    unfold fl4_abi.label.X86PageDirectoryMap fl4_abi.label.X86PageDirectoryUnmap; decide
  simp only [vspace.as_table, bind_ok, hne, ↓reduceIte]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte] at hDec ⊢
    unfold vspace.decode_table_map
    rw [hct]
    apply ok_bind_spec
    rw [hex]
    apply ok_bind_spec
    dsimp only
    by_cases h2 : length >= 2#u64
    · rw [if_pos h2]
      have h2' : 2 ≤ args.length := by
        have : 2 ≤ length.val := by scalar_tac
        omega
      obtain ⟨a0, a1, ar', rfl⟩ : ∃ a0 a1 r', args = a0 :: a1 :: r' := by
        match args, h2' with
        | a0 :: a1 :: r', _ => exact ⟨_, _, _, rfl⟩
      simp only [List.map_cons] at hDec
      rw [hargs 0#u64 a0 (by simp)]; apply ok_bind_spec
      unfold lift
      simp only [bind_ok, shl30]
      rw [hargs 1#u64 a1 (by simp)]; apply ok_bind_spec
      rw [slot_cap_eq, hcx]; apply ok_bind_spec
      generalize hvd : a0 &&& ~~~core.num.U64.wrapping_sub 1073741824#u64 1#u64 = v
      have hvb : v.bv = a0.bv &&& ~~~Fl4Spec.mask Fl4Spec.pdptShiftBits := by rw [← hvd]; exact vaddr30_bv a0
      by_cases hvp : ∃ p asid, vc = .Pml4 p true asid
      · obtain ⟨p1, as1, rfl⟩ := hvp
        obtain ⟨hp1, has1, has2⟩ := hvc p1 as1 rfl
        have hvc' : vc' = .archObjectCap (.pml4Cap p1.bv (some as1.bv)) := by rw [← hvr.2]; rfl
        subst hvc'
        have hdec : D = ExceptT.run (pdTail ptr.bv p1.bv as1.bv v.bv a1.bv (pc.bv, idx)) σ := by
          rw [← hDec, pdDecode_body hl, hvb]
        simp only [vspace.is_valid_vtable_root, ↓reduceIte, bind_ok]
        by_cases hv : v > fl4_abi.consts.USER_TOP
        · simp only [hv, ↓reduceIte, error.invalid_arg, bind_ok]
          exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
            Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl),
            hdec.trans (pdTail_top ((top_bv v).2 hv)), rfl, rfl⟩)
        have hv' : ¬ Fl4Spec.userVtop < v.bv := fun h => hv ((top_bv v).1 h)
        have hva : v.val < 2 ^ 48 := by
          have := hv
          rw [gt_iff_val] at this
          have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
          omega
        simp only [hv, ↓reduceIte]
        refine WP.spec_bind (check_vspace_pml4_pd s σ hR p1 as1 has1 ptr.bv v.bv a1.bv (pc.bv, idx) hv') ?_
        rintro r1 (⟨rfl, hf⟩ | ⟨e, e', rfl, he, hte⟩)
        rotate_left
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
          simp only [Bind.bind, bind_ok]
          exact (WP.spec_ok _).2 (Or.inl ⟨e, e', rfl, he, hdec.trans hte, rfl, rfl⟩)
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        refine WP.spec_bind (table_entry_slot_30 s σ hPt hPP hp1 v (userV_of_not_gt hv)) ?_
        rintro r2 ⟨hsl, hse⟩
        cases r2 with
        | Err lf =>
          obtain ⟨n, rfl, hsp⟩ := hse _ rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from]
          simp only [Bind.bind, bind_ok]
          exact (WP.spec_ok _).2 (Or.inl ⟨_, .failedLookup false (.missingCapability n.val), rfl,
            Or.inl (by simp [SysErrRel, LookupFaultRel]), hdec.trans (pdTail_noSlot hv' hf hsp), rfl, rfl⟩)
        | Ok sl =>
          obtain ⟨hsp, q, hq, rfl⟩ := hsl _ rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          obtain ⟨f, hk, hf2⟩ := hPt.l3 q hq
          have hqa := hPP q (Or.inr (Or.inl hq))
          have hj := vIdx_lt v 30
          have hfe2 := hf2 _ hj
          have hg : Fl4Spec.getPdpte (Z := Unit) (peA q (vIdx v 30)).bv σ =
              ({(f (Fl4Spec.ucast 9 (vIdx v 30).bv), σ)}, False) := by
            rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPdpte_at hqa hk hj
          rw [L.read_eq]
          apply ok_bind_spec
          rw [P_PRESENT_eq]
          apply ok_bind_spec
          by_cases hpres : (L.mem s (peA q (vIdx v 30)) &&& 1#u64) = 0#u64
          · have : ((L.mem s (peA q (vIdx v 30)) &&& 1#u64) != 0#u64) = false := by simp [hpres]
            simp only [this, Bool.false_eq_true, ↓reduceIte]
            have hinv : f (Fl4Spec.ucast 9 (vIdx v 30).bv) = .invalidPDPTE := by
              revert hfe2
              cases f (Fl4Spec.ucast 9 (vIdx v 30).bv) with
              | invalidPDPTE => intro; rfl
              | pageDirectoryPDPTE _ _ _ => intro h; exact absurd hpres h.1
              | hugePagePDPTE _ _ _ => intro h; exact absurd hpres h.1
            rw [hinv] at hg
            simp only [layout.paddr, bind_ok]
            refine WP.spec_bind (make_user_table_spec _ a1) ?_
            rintro e he
            set pde : Fl4Spec.PDPTE := .pageDirectoryPDPTE (Fl4Spec.addrFromPPtr ptr.bv)
              (Fl4Spec.filterVmAttributes (Fl4Spec.attribsFromWord a1.bv)) Fl4Spec.vmReadWrite with hpdeD
            have hpde : PDPTERel L2 e pde := pdpte_of_make hpL2 hpa he _ _
            have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
            refine WP.spec_bind (WP.spec_and (hH.restart s a σ ct xct hSt hSV hR hPt hS hcur hkt' htcb hact hrun)
              (set_thread_state_slots th hPl s ct sched.TS_RESTART htcb hact)) ?_
            rintro s1 ⟨⟨hSt1, hSV1, hR1, hPt1, hS1, hk1⟩, hSS1⟩
            set σ1 := stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv with hσ1
            obtain ⟨cs, hkc, hwf, -⟩ := hSt.cnode pc r hpc
            have hpct : pc.bv ≠ ct.bv := kheap_ne hkc hkt' (fun _ h1 h2 => by subst h1; cases h2)
            have hkc1 : σ1.kheap pc.bv = some (.cnode r cs) := by
              rw [hσ1, stsAct_kheap]; simp [updK, hpct, hkc]
            rw [show vspace.with_mapping (.PageDirectory ptr false asid0 va0) true as1 v = ok (.PageDirectory ptr true as1 v)
              by simp [vspace.with_mapping]]
            apply ok_bind_spec
            set nc : Fl4Spec.Cap := .archObjectCap (.pageDirectoryCap ptr.bv (some (as1.bv, v.bv))) with hnc
            have hca : CapRel (.PageDirectory ptr true as1 v) nc := ⟨trivial, rfl⟩
            have hew : EncWf (.PageDirectory ptr true as1 v) := ⟨hfe.1, has2, hva⟩
            have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
              (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
            refine WP.spec_bind (WP.spec_and (set_cap_refines th s1 σ1 hSt1 hSV1 hPl hpc hidx _ _ hca trivial hew)
              (WP.spec_and (set_cap_spec (L := L) _ s1 _) (set_cap_foot hPl hxsl s1 _ hew))) ?_
            rintro s2 ⟨⟨σ2, hsc, hSt2, hSV2, -, -, -, hfr2⟩, hs2, hF2, hcv2⟩
            have hσ2 : σ2 = setCnodeSlot σ1 pc.bv r cs idx nc := by
              rw [setCap_cnode nc hkc1 hwf hidx] at hsc
              have := congrArg Prod.fst hsc
              simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
              exact this.symm
            subst hσ2
            have hks2 : L.ksb s2 = L.ksb s := by rw [hs2]; simp [hk1]
            have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
            have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
            have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s2 b = L.mem s1 b := by
              intro b hb
              obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
              exact hfr2 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
            have hpools : ∀ q ∈ P, (setCnodeSlot σ1 pc.bv r cs idx nc).kheap q.bv = σ1.kheap q.bv := by
              intro q hq
              obtain ⟨g, hg, -⟩ := hR1.pool q hq
              have : q.bv ≠ pc.bv := kheap_ne hg hkc1 (fun _ h1 h2 => by subst h1; cases h2)
              simp [setCnodeSlot, this]
            have hR2 : VsRel P (L.mem s2) (L.ksb s2) (setCnodeSlot σ1 pc.bv r cs idx nc) := by
              rw [hks2]; rw [hk1] at hR1
              exact hR1.frame hfrV rfl hpools
            have hWs : WritesIn st s1 s2 (SlotW th) := by
              refine ⟨by rw [hs2]; simp, by rw [hs2]; simp, fun b hb hn => ?_⟩
              obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
              exact hfr2 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
            have hS2 := hH.capStable _ _ a _ _ hS1 hWs ⟨pc.bv, r, cs, idx, nc, hkc1, rfl⟩
            have hPt2 : PtRel L4 L3 L2 L1 (L.mem s2) (setCnodeSlot σ1 pc.bv r cs idx nc) := by
              refine hPt1.frame (fun b hb => ?_) (fun q hq => ?_)
              · obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hPS b hb)
                exact hfr2 b (hb.aligned hPP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
              · obtain ⟨ao, hao⟩ := hPt1.arch hq
                have : q.bv ≠ pc.bv := kheap_ne hao hkc1 (fun _ h1 h2 => by subst h1; cases h2)
                simp [setCnodeSlot, this]
            -- the PD entry
            set σ2 := setCnodeSlot σ1 pc.bv r cs idx nc with hσ2
            obtain ⟨f2, hk2, -⟩ := hPt2.l3 q hq
            have hea : Aligned (peA q (vIdx v 30)) := by
              show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
            rw [L.write_eq]
            apply ok_bind_spec
            set s3 := L.wr s2 (peA q (vIdx v 30)) e with hs3
            set σ3 := updK σ2 q.bv (.archObj (.pdPointerTable (Function.update f2 (Fl4Spec.ucast 9 (vIdx v 30).bv) pde)))
              with hσ3
            have hstore : Fl4Spec.storePdpte (Z := Unit) (peA q (vIdx v 30)).bv pde σ2 = ({((), σ3)}, False) := by
              rw [peA_bv _ _ hj (tbl_fit hqa)]; exact storePdpte_at hqa hk2 hj pde
            have hPt3 : PtRel L4 L3 L2 L1 (L.mem s3) σ3 :=
              hPt2.upd_l3 hPP hq hk2 hj e pde hpde
                (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
            have hW : WritesIn st s2 s3 (PdptW L3) :=
              ⟨by simp [hs3], by simp [hs3], fun b hb hn => L.mem_wr_ne hea hb
                (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
            have hS3 := hH.pdptStable _ _ a σ2 σ3 hS2 hW ⟨q.bv, f2, _, hk2, rfl⟩
            have hPS2 : ∀ b, PdptW L3 b → ¬ SlotW th b := by
              rintro b ⟨p, hp, i, hi, hb⟩
              exact hPS b ⟨p, Or.inr (Or.inl hp), i, hi, hb⟩
            have hcap := capAt_of_writes hPl hW hPS2
            have hSt3 : StateRel th (L.mem s3) σ3 := Vs.StateRel.upd_other (StateRel.of_caps hSt2 hcap) hk2 _
            have hSV3 : SlotsValid th (L.mem s3) := Vs.SlotsValid.of_caps hSV2 hcap
            have hR3 : VsRel P (L.mem s3) (L.ksb s3) σ3 := by
              rw [hW.1]
              refine hR2.frame (fun b hb => hW.2.2 b (hb.aligned (hks2 ▸ hVP))
                (fun h => hPV b h (hks2 ▸ hb))) rfl (fun p hp => ?_)
              obtain ⟨g, hg, -⟩ := hR2.pool p hp
              have : p.bv ≠ q.bv := kheap_ne hg hk2 (fun _ h1 h2 => by subst h1; cases h2)
              simp [hσ3, updK, this]
            refine WP.spec_bind (hH.flushPS s3 a σ3 (Fl4Spec.addrFromPPtr p1.bv) as1 hS3) ?_
            rintro a4 ⟨σ', hm, hS'⟩
            have hm' := hm
            obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
            have hbo : OutsideObjects th (peA q (vIdx v 30)) := hPO _ ⟨q, Or.inr (Or.inl hq), _, hj, rfl⟩
            refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, _, hdec.trans (pdTail_ok hv' hf hsp hg), ?_,
              Vs.StateRel.ms hSt3 ms, hSV3, ⟨hR3.1, hR3.2, hR3.3⟩, ⟨hPt3.l4, hPt3.l3, hPt3.l2, hPt3.l1⟩, hS', ?_, ?_, ?_⟩)
            · unfold PdMapSpec pdInv
              dsimp only
              rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
              exact performPdMap_mem (setCap_cnode nc hkc1 hwf hidx) hstore hm' (hH.flushOK _ _ _)
            · exact (SlotFoot.of_same hSS1 _).trans (hF2.trans (SlotFoot.wr_out hPl s2 hbo _))
            · show VsLike (capV (L.mem s3) _) _
              rw [hs3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK] at h ⊢; exact ⟨h.1, h.2.1, fun _ => has1, fun _ => userV_of_not_gt hv⟩⟩
            · exact (KFoot.sts hkt' _).trans ((KFoot.cnode hkc1 hwf idx nc).trans ((KFoot.arch hk2 _).trans (KFoot.ms _ ms)))
          · have : ((L.mem s (peA q (vIdx v 30)) &&& 1#u64) != 0#u64) = true := by simp [hpres]
            simp only [this, ↓reduceIte]
            have hninv : f (Fl4Spec.ucast 9 (vIdx v 30).bv) ≠ .invalidPDPTE := by
              intro h; rw [h] at hfe2; exact hfe2 hpres
            exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl, Or.inl (show SysErrRel _ .deleteFirst from trivial),
              hdec.trans (pdTail_used hv' hf hsp hg hninv), rfl, rfl⟩)
      · have hmr : vspace.is_valid_vtable_root vc = ok false := by
          cases vc <;> simp_all [vspace.is_valid_vtable_root]
        rw [hmr]
        simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, error.invalid_cap]
        have hbad : ∀ pm asid, vc' ≠ .archObjectCap (.pml4Cap pm (some asid)) := by
          intro pm asid h
          rw [← hvr.2] at h
          cases vc <;> simp_all [absCap]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inr ⟨1#u64, rfl, rfl⟩,
          hDec ▸ pdDecode_badVs hl _ _ _ _ _ _ _ _ hbad σ, rfl, rfl⟩)
    · rw [if_neg h2]
      simp only [error.truncated, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl,
        Or.inl (show SysErrRel (.Sys .TruncatedMessage) .truncatedMessage from trivial),
        hDec ▸ pdDecode_trunc hl _ _ _ _ _ ?_ σ, rfl, rfl⟩)
      have : length.val < 2 := by scalar_tac
      simp only [List.length_map]; omega
  · simp only [↓reduceIte] at hDec ⊢
    rw [hex]
    apply ok_bind_spec
    dsimp only
    by_cases h2 : length >= 2#u64
    · rw [if_pos h2]
      have h2' : 2 ≤ args.length := by
        have : 2 ≤ length.val := by scalar_tac
        omega
      obtain ⟨a0, a1, ar', rfl⟩ : ∃ a0 a1 r', args = a0 :: a1 :: r' := by
        match args, h2' with
        | a0 :: a1 :: r', _ => exact ⟨_, _, _, rfl⟩
      simp only [List.map_cons] at hDec
      simp only [error.invalid_cap, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩,
        hDec ▸ pdDecode_mapped hl _ _ _ _ _ _ _ _ σ, rfl, rfl⟩)
    · rw [if_neg h2]
      simp only [error.truncated, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl,
        Or.inl (show SysErrRel (.Sys .TruncatedMessage) .truncatedMessage from trivial),
        hDec ▸ pdDecode_trunc hl _ _ _ _ _ ?_ σ, rfl, rfl⟩)
      have : length.val < 2 := by scalar_tac
      simp only [List.length_map]; omega

end

end

end Fl4Proofs.P3.Vs
