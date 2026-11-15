/-
P3 (DESIGN.md §9), VSpace: **Frame `Map` for 4K pages refines l4v**
(`decode_page_invocation`, then `set_thread_state cur Restart`, then
`perform_page_invocation`).

`frame_map_rel`: FL4's `vspace::decode_page_map` on a 4K frame cap in a
CNode slot, with a first extra cap `vc` (related to l4v's `vc'`), either
* fails with an error related to the spec decode's error (`MapErrRel`), the
  states unchanged, or
* succeeds, the spec decodes the page map `iv` (deterministically), and
  `set_thread_state cur Restart` followed by `perform_page_invocation iv`
  does not fail and has an outcome `σ'` related again: CSpace `StateRel` and
  `SlotsValid`, the ASID relation `VsRel`, the page tables `PtRel`, and `SR`.

Hypotheses (`VsFrameHyps`): setting the current thread `Restart`
(`restart`), `SR` stable under the slot write (`capStable`), and the TLB
flushes with `SR` (`map : VsMapHyps`). Invariants taken as hypotheses:
* the page-table words (`PtWAll`) are not slot words, and the PT entry
  words are not ASID-table or pool words;
* a mapped frame cap has a non-zero ASID; a mapped PML4 cap names a PML4 of
  `L4` and has a non-zero 20-bit ASID (l4v `valid_cap`);
* the frame's physical address is 4K-aligned and below 2^52
  (`(paddr ptr) & ADDR_MASK = paddr ptr`).
-/
import Fl4Proofs.P3.VsFrameMap
import Fl4Proofs.P3.CnodeCaps
import Fl4Proofs.P3.VsFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- The native projection of a decoded frame, for the native mapping helper. -/
def frameCapOf (f : vspace.FrameCap) : capability.Cap :=
  .Frame f.ptr f.size f.rights f.is_device f.mapped false f.asid f.vaddr

/-- The spec's cap of a decoded 4K frame. -/
def frameACap (f : vspace.FrameCap) : Fl4Spec.ArchCap :=
  .pageCap f.is_device f.ptr.bv (vmRightsOf f.rights) (if f.mapped then .vmVSpaceMap else .vmNoMap) .x64SmallPage
    (if f.mapped then some (f.asid.bv, f.vaddr.bv) else none)

/-- The errors of the frame map: `VsErrRel`, and alignment. -/
def MapErrRel (e : error.Exc) (e' : Fl4Spec.SyscallError) : Prop :=
  VsErrRel e e' ∨ (e = .Sys .AlignmentError ∧ e' = .alignmentError)

/-- The entry words of all page tables. -/
def PtWAll (L4 L3 L2 L1 : Set U64) (b : U64) : Prop :=
  ∃ p, (p ∈ L4 ∨ p ∈ L3 ∨ p ∈ L2 ∨ p ∈ L1) ∧ ∃ i : U64, i.val < 512 ∧ b = peA p i

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- `SR` with the CSpace and ASID relations, for `write_mapping_rel`. -/
def MapRel {A : Type} (th : TypedHeap) (P L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ StateRel th (L.mem s) σ ∧ SlotsValid th (L.mem s) ∧ VsRel P (L.mem s) (L.ksb s) σ ∧
    VsPlaced P (L.ksb s) ∧ ∀ b, PtW L1 b → ¬ VsWrite P (L.ksb s) b

/-- The hypotheses of the frame map (see the module docstring). -/
structure VsFrameHyps (A : Type) (ar : machine.Arch A) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
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
  map : VsMapHyps st A ar L1 SR

end Hyps

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The flushes and stability for `MapRel`. -/
theorem VsMapHyps.ext {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsMapHyps st A ar L1 SR) (hPl : Placed th)
    (hPS : ∀ b, PtW L1 b → ¬ SlotW th b) : VsMapHyps st A ar L1 (MapRel st th P L1 SR) where
  stable s s' a σ σ' := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩ hW hst
    have hS' := hH.stable s s' a σ σ' hS hW hst
    obtain ⟨p, f, f', hk, rfl⟩ := hst
    have hcap := capAt_of_writes hPl hW hPS
    refine ⟨hS', Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _, Vs.SlotsValid.of_caps hSV hcap, ?_,
      by rw [hW.1]; exact hVP, by rw [hW.1]; exact hPV⟩
    rw [hW.1]
    refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b h hb)) rfl (fun q hq => ?_)
    obtain ⟨g, hg, -⟩ := hR.pool q hq
    have : q.bv ≠ p := kheap_ne hg hk (fun _ h1 h2 => by subst h1; cases h2)
    simp [updK, this]
  flushOK := hH.flushOK
  noFlush s a σ vs asid := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩
    obtain ⟨σ', h1, h2⟩ := hH.noFlush s a σ vs asid hS
    obtain ⟨ms, rfl⟩ := doMachineOp_mem h1
    exact ⟨_, h1, h2, Vs.StateRel.ms hSt ms, hSV, ⟨hR.1, hR.2, hR.3⟩, hVP, hPV⟩
  flushPage s a σ vs asid vaddr := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩
    refine WP.spec_mono (hH.flushPage s a σ vs asid vaddr hS) ?_
    rintro a' ⟨σ', h1, h2⟩
    obtain ⟨ms, rfl⟩ := doMachineOp_mem h1
    exact ⟨_, h1, h2, Vs.StateRel.ms hSt ms, hSV, ⟨hR.1, hR.2, hR.3⟩, hVP, hPV⟩
  flushAsid s a σ vs asid := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩
    refine WP.spec_mono (hH.flushAsid s a σ vs asid hS) ?_
    rintro a' ⟨σ', h1, h2⟩
    obtain ⟨ms, rfl⟩ := doMachineOp_mem h1
    exact ⟨_, h1, h2, Vs.StateRel.ms hSt ms, hSV, ⟨hR.1, hR.2, hR.3⟩, hVP, hPV⟩

/-- The page-table relation only reads the table words and the tables. -/
theorem PtRel.frame {L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (hR : PtRel L4 L3 L2 L1 m σ) (hm : ∀ b, PtWAll L4 L3 L2 L1 b → m' b = m b)
    (hk : ∀ q, (q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → σ'.kheap q.bv = σ.kheap q.bv) :
    PtRel L4 L3 L2 L1 m' σ' := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l4 q hq
    exact ⟨g, (hk q (Or.inl hq)).trans hg, fun j hj => by rw [hm _ ⟨q, Or.inl hq, j, hj, rfl⟩]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l3 q hq
    exact ⟨g, (hk q (Or.inr (Or.inl hq))).trans hg,
      fun j hj => by rw [hm _ ⟨q, Or.inr (Or.inl hq), j, hj, rfl⟩]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l2 q hq
    exact ⟨g, (hk q (Or.inr (Or.inr (Or.inl hq)))).trans hg,
      fun j hj => by rw [hm _ ⟨q, Or.inr (Or.inr (Or.inl hq)), j, hj, rfl⟩]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l1 q hq
    exact ⟨g, (hk q (Or.inr (Or.inr (Or.inr hq)))).trans hg,
      fun j hj => by rw [hm _ ⟨q, Or.inr (Or.inr (Or.inr hq)), j, hj, rfl⟩]; exact hgf j hj⟩

/-- Every table is a page-table object of the spec. -/
theorem PtRel.arch {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ : Fl4Spec.State Unit}
    (hR : PtRel L4 L3 L2 L1 m σ) {q : U64} (hq : q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) :
    ∃ ao, σ.kheap q.bv = some (.archObj ao) := by
  rcases hq with hq | hq | hq | hq
  · obtain ⟨g, hg, -⟩ := hR.l4 q hq; exact ⟨_, hg⟩
  · obtain ⟨g, hg, -⟩ := hR.l3 q hq; exact ⟨_, hg⟩
  · obtain ⟨g, hg, -⟩ := hR.l2 q hq; exact ⟨_, hg⟩
  · obtain ⟨g, hg, -⟩ := hR.l1 q hq; exact ⟨_, hg⟩

theorem PtWAll.aligned {L4 L3 L2 L1 : Set U64} (hP : PtPlaced L4 L3 L2 L1) {b : U64} (h : PtWAll L4 L3 L2 L1 b) :
    Aligned b := by
  obtain ⟨p, hp, i, hi, rfl⟩ := h
  have := hP p hp
  show _ % 8 = 0; rw [peA_val (tbl_fit this) hi]; omega

/-- FL4's lookup faults of `find_vspace_for_asid`. -/
theorem find_asid_err (s : S) (asid : U64) :
    vspace.find_asid st s asid ⦃ r => ∀ e, r = .Err e → e = .InvalidRoot ⦄ := by
  unfold vspace.find_asid
  have hL : vspace.ASID_LOW_BITS = 9#u64 := by unfold vspace.ASID_LOW_BITS; rfl
  rw [hL]
  step as ⟨i, _hi⟩
  refine WP.spec_bind (asid_table_spec s i) ?_
  rintro pool -
  split
  · exact (WP.spec_ok _).2 fun e he => by cases he; rfl
  · unfold lift
    simp only [bind_ok]
    rw [L.read_eq]
    simp only [bind_ok]
    split
    · exact (WP.spec_ok _).2 fun e he => by cases he; rfl
    · exact (WP.spec_ok _).2 fun e he => by cases he

theorem find_vspace_for_asid_err (s : S) (asid : U64) :
    vspace.find_vspace_for_asid st s asid ⦃ r => ∀ e, r = .Err e → e = .InvalidRoot ⦄ := by
  unfold vspace.find_vspace_for_asid
  refine WP.spec_bind (find_asid_err s asid) ?_
  intro r hr
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.convert.FromSame, bind_ok, WP.spec_ok]
    simpa only [WP.spec_ok, core.convert.FromSame, core.convert.FromSame.from, lift, bind_ok, bind_tc_ok] using hr
  | Ok w =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, lift, bind_ok]
    split <;> simp only [WP.spec_ok] <;> intro e he <;> cases he <;> rfl

theorem shl12 : (1#u64 <<< (12#u64 &&& 63#u64)) = ok 4096#u64 := by
  rw [and63_of_lt (by decide), shl_u64_eq _ _ (by decide)]; rfl

theorem al12 (v : U64) : (v &&& 4095#u64) = 0#u64 ↔ Fl4Spec.isAligned v.bv 12 := by
  unfold Fl4Spec.isAligned
  have : (v &&& 4095#u64).val = v.val % 4096 := by
    rw [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod v.val 12
  constructor
  · intro h; rw [h] at this; exact Nat.dvd_of_mod_eq_zero (by simpa using this.symm)
  · intro h; apply UScalar.eq_of_val_eq; rw [this, Nat.mod_eq_zero_of_dvd (show 4096 ∣ v.val from h)]; rfl

theorem paddr_bv (p : U64) : (core.num.U64.wrapping_sub p layout.PPTR_BASE).bv = Fl4Spec.addrFromPPtr p.bv := by
  rw [core.num.U64.wrapping_sub_bv_eq]; unfold layout.PPTR_BASE; rfl

theorem attr_defer (w : U64) :
    Fl4Spec.attribsFromWord (w &&& ~~~fl4_abi.consts.vm_attr.DEFER_FLUSH).bv = Fl4Spec.attribsFromWord w.bv := by
  have hc : (w &&& ~~~fl4_abi.consts.vm_attr.DEFER_FLUSH).bv = w.bv &&& ~~~16#64 := by
    unfold fl4_abi.consts.vm_attr.DEFER_FLUSH; rfl
  have hb : ∀ k, k < 3 → (w &&& ~~~fl4_abi.consts.vm_attr.DEFER_FLUSH).bv.getLsbD k = w.bv.getLsbD k := by
    intro k hk
    rw [hc, BitVec.getLsbD_and]
    have : (~~~16#64 : BitVec 64).getLsbD k = true := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide
    rw [this, Bool.and_true]
  unfold Fl4Spec.attribsFromWord Fl4Spec.testBit
  rw [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide)]

theorem vm_eq {rt m : U64} (r : capability.Rights) (w : U64) (hr : r = rightsW w)
    (hmv : vmRightsOf m = Fl4Spec.validateVmRights (vmRightsOf rt ∩ rightsOf r.write r.read r.grant r.grant_reply)) :
    vmRightsOf m = Fl4Spec.maskVmRights (vmRightsOf rt) (Fl4Spec.dataToRights w.bv) := by
  subst hr; rw [hmv, rightsW_spec]; rfl

theorem vmOk_of {m : U64} (h1 : 1 ≤ m.val) (h3 : m.val ≤ 3) : VmRightsOk m := by
  unfold VmRightsOk capability.VM_KERNEL_ONLY capability.VM_READ_ONLY capability.VM_READ_WRITE
  have : m.val = 1 ∨ m.val = 2 ∨ m.val = 3 := by omega
  rcases this with h | h | h
  · left; exact UScalar.eq_of_val_eq (by simpa using h)
  · right; left; exact UScalar.eq_of_val_eq (by simpa using h)
  · right; right; exact UScalar.eq_of_val_eq (by simpa using h)

/-- `check_vspace` on a mapped PML4 cap: the root, or the decode's error. -/
theorem check_vspace_pml4 {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (p asid : U64) (h0 : asid ≠ 0#u64) (dev : Bool) (pp : Fl4Spec.ObjRef) (R : Fl4Spec.VMRights)
    (va rm at' : Fl4Spec.Data) (cte : Fl4Spec.CslotPtr) :
    vspace.check_vspace st s (.Pml4 p true asid) ⦃ r =>
      (r = .Ok (p, asid) ∧
        ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False)) ∨
      (∃ e e', r = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (mapTail p.bv asid.bv dev pp R va rm at' cte) σ = ({(.error e', σ)}, False)) ⦄ := by
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
      exact (WP.spec_ok _).2 (Or.inr ⟨_, _, rfl, Or.inr ⟨1#u64, rfl, rfl⟩, mapTail_wrongVs hf (fun h => hr (eq_of_bv h))⟩)
  | Err lf =>
    obtain rfl := he lf rfl
    refine (WP.spec_ok _).2 (Or.inr ⟨_, _, rfl, Or.inl (show SysErrRel (.Sys (.FailedLookup false .InvalidRoot))
      (.failedLookup false .invalidRoot) by simp [SysErrRel, LookupFaultRel]), mapTail_noVs hf⟩)

theorem gt_top (v : U64) : (v.bv > Fl4Spec.userVtop) ↔ v > fl4_abi.consts.USER_TOP := by
  have hU : fl4_abi.consts.USER_TOP.val = Fl4Spec.userVtop.toNat := by unfold fl4_abi.consts.USER_TOP; rfl
  rw [gt_iff_val, hU]; exact BitVec.lt_def

theorem add4096 (v : U64) : (core.num.U64.wrapping_add v 4096#u64).bv = v.bv + 4096 := by
  rw [core.num.U64.wrapping_add_bv_eq]; rfl

theorem page_entry_slot_small {L4 L3 L2 L1 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64) :
    vspace.page_entry_slot st s pm vaddr .Small ⦃ r =>
      (∀ x, r = .Ok x → ExceptT.run (Fl4Spec.lookupPtSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(.ok x.bv, σ)}, False) ∧
        ∃ q ∈ L1, x = peA q (vIdx vaddr 12)) ∧
      (∀ e, r = .Err e → ∃ n, e = .Sys (.FailedLookup false (.MissingCapability n)) ∧
        ExceptT.run (Fl4Spec.lookupPtSlot (Z := Unit) pm.bv vaddr.bv) σ =
          ({(.error (.missingCapability n.val), σ)}, False)) ⦄ := by
  unfold vspace.page_entry_slot
  refine WP.spec_bind (lookup_pt_slot_rel s σ hR hP hpm vaddr) ?_
  rintro r ⟨hsp, hsl, hse⟩
  cases r with
  | Ok x =>
    simp only [↓reduceIte, bind_ok]
    exact (WP.spec_ok _).2 ⟨(fun y hy => by cases hy; exact ⟨hsp, hsl _ rfl⟩), fun e he => by cases he⟩
  | Err lf =>
    obtain ⟨n, rfl⟩ := hse _ rfl
    exact (WP.spec_ok _).2 ⟨(fun y hy => by cases hy), fun e he => by cases he; exact ⟨n, rfl, hsp⟩⟩

/-- The spec's footprint of a PT store and its flush. -/
theorem kfoot_store_flush {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L1) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PTE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePte (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : KFoot σ2 σ' := by
  obtain ⟨f, hk, -⟩ := hR.l1 q hq
  have hpa := hP q (Or.inr (Or.inr (Or.inr hq)))
  have hst : Fl4Spec.storePte (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pageTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePte_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  exact (KFoot.arch hk _).trans (KFoot.ms _ ms)

set_option hygiene false in
/-- The common part of both cases: from `check_vspace` on. -/
macro "map_tail" : tactic => `(tactic| (
  refine WP.spec_bind (check_vspace_pml4 s σ hR p1 as1 has1 dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) ?_
  rintro r1 (⟨rfl, hf⟩ | ⟨e, e', rfl, he, hte⟩)
  rotate_left
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    simp only [Bind.bind, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨e, e', rfl, Or.inl he, hdec.trans hte, rfl, rfl⟩)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, from_word_eq]
  obtain ⟨m, hm, hm1, hm3, hmv⟩ := vm_mask rt hfw (rightsW a1)
  rw [hm]
  apply ok_bind_spec
  rw [show core.num.U64.wrapping_sub 4096#u64 1#u64 = 4095#u64 from eq_of_bv (by rw [core.num.U64.wrapping_sub_bv_eq]; decide)]
  by_cases hal : (a0 &&& 4095#u64) = 0#u64
  · have : ((a0 &&& 4095#u64) != 0#u64) = false := by simp [hal]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (page_entry_slot_small s σ hPt hPP hp1 a0) ?_
    rintro r3 ⟨hsl, hse⟩
    cases r3 with
    | Err lf =>
      obtain ⟨n, rfl, hsp⟩ := hse _ rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      simp only [Bind.bind, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .failedLookup false (.missingCapability n.val), rfl,
        Or.inl (Or.inl (by simp [SysErrRel, LookupFaultRel])),
        hdec.trans (mapTail_noSlot hf ((al12 a0).1 hal) hsp), rfl, rfl⟩)
    | Ok sl =>
      obtain ⟨hsp, q, hq, rfl⟩ := hsl _ rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, layout.paddr]
      refine WP.spec_bind (make_user_page_4k s _ _ m) ?_
      rintro e ⟨xd, he⟩
      have hpte := pte_of_make (vmOk_of hm1 hm3) he
      rw [hpa] at hpte
      simp only [paddr_bv, attr_defer, vm_eq (rightsW a1) a1 rfl hmv] at hpte
      have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
      refine WP.spec_bind (WP.spec_and (hH.restart s a σ ct xct hSt hSV hR hPt hS hcur hkt' htcb hact hrun)
        (set_thread_state_slots th hPl s ct sched.TS_RESTART htcb hact)) ?_
      rintro s1 ⟨⟨hSt1, hSV1, hR1, hPt1, hS1, hk1⟩, hSS1⟩
      set σ1 := stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv with hσ1
      obtain ⟨cs, hkc, hwf, -⟩ := hSt.cnode pc r hpc
      have hpct : pc.bv ≠ ct.bv := kheap_ne hkc hkt' (fun _ h1 h2 => by subst h1; cases h2)
      have hkc1 : σ1.kheap pc.bv = some (.cnode r cs) := by
        rw [hσ1, stsAct_kheap]; simp [updK, hpct, hkc]
      set nc : Fl4Spec.Cap := .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt) .vmVSpaceMap .x64SmallPage
        (some (as1.bv, a0.bv))) with hnc
      have hca : CapRel (.Frame ptr .Small rt dev true false as1 a0) nc := ⟨hfw, rfl⟩
      have hew : EncWf (.Frame ptr .Small rt dev true false as1 a0) := ⟨hfe.1, hfe.2.1, has2, hva⟩
      have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
        (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
      refine WP.spec_bind (WP.spec_and (set_cap_refines th s1 σ1 hSt1 hSV1 hPl hpc hidx _ _ hca (by exact hfcv) hew)
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
      have hPS1 : ∀ b, PtW L1 b → ¬ SlotW th b := by
        rintro b ⟨p, hp, i, hi, hb⟩
        exact hPS b ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, hb⟩
      have hMR : MapRel st th P L1 SR s2 a (setCnodeSlot σ1 pc.bv r cs idx nc) :=
        ⟨hS2, hSt2, hSV2, hR2, by rw [hks2]; exact hVP, by rw [hks2]; exact hPV⟩
      refine WP.spec_bind (write_mapping_rel (hH.map.ext hPl hPS1) s2 a _ hPt2 hPP hMR hq (vIdx_lt a0 12) e _ hpte
        as1 a0 _ (Fl4Spec.addrFromPPtr p1.bv)) ?_
      rintro ⟨s3, a3⟩ ⟨hr3, hnf, σ', hm', hPt3, hS3, hSt3, hSV3, hR3, -, -⟩
      have hbo : OutsideObjects th (peA q (vIdx a0 12)) := hPO _ ⟨q, Or.inr (Or.inr (Or.inr hq)), _, vIdx_lt a0 12, rfl⟩
      simp only at hr3
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, σ', hdec.trans (mapTail_ok hf ((al12 a0).1 hal) hsp), ?_,
        hSt3, hSV3, hR3, hPt3, hS3, ?_, ?_, ?_⟩)
      · unfold MapSpec mapInv
        dsimp only
        rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
        exact performMap_mem (setCap_cnode nc hkc1 hwf hidx) hm' hnf
      · rw [hr3]
        exact (SlotFoot.of_same hSS1 _).trans (hF2.trans (SlotFoot.wr_out hPl s2 hbo _))
      · rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK, frameCapOf] at h ⊢; exact ⟨fun _ => has1, h.2⟩⟩
      · exact (KFoot.sts hkt' _).trans ((KFoot.cnode hkc1 hwf idx nc).trans
          (kfoot_store_flush hPP hPt2 hq (vIdx_lt a0 12) _ _ _ hm'))
  · have : ((a0 &&& 4095#u64) != 0#u64) = true := by simp [hal]
    simp only [this, ↓reduceIte]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩,
      hdec.trans (mapTail_unaligned hf (fun h => hal ((al12 a0).2 h))), rfl, rfl⟩)))

/-- **4K Frame `Map` refines l4v** (see the module docstring). -/
theorem frame_map_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtW L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (hsz : f.size = .Small) (hfw : CapWf (frameCapOf f)) (hfe : EncWf (frameCapOf f)) (hfcv : CapValid th (frameCapOf f))
    (hfm : f.mapped = true → f.asid ≠ 0#u64)
    (hpa : (core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_page_map st ar s a length (cslotAddr (pc.bv, idx)) f buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) xs (pc.bv, idx)
          (frameACap f) ((vc', xsl) :: rest)) σ = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) xs
          (pc.bv, idx) (frameACap f) ((vc', xsl) :: rest)) σ = ({(.ok iv, σ)}, False) ∧
        MapSpec σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf f) ∧ KFoot σ σ') ⦄ := by
  obtain ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩ := f
  simp only at hsz hfm hpa ⊢
  subst hsz
  rw [show ∀ args' ex', Fl4Spec.archDecodeInvocation (Z := Unit) slbl args' xs (pc.bv, idx)
      (frameACap ⟨ptr, .Small, rt, dev, mp, ep, fa, fv⟩) ex' =
    Fl4Spec.decodePageInvocation slbl args' (pc.bv, idx) (.pageCap dev ptr.bv (vmRightsOf rt)
      (if mp then .vmVSpaceMap else .vmNoMap) .x64SmallPage (if mp then some (fa.bv, fv.bv) else none)) ex' from
    fun _ _ => rfl]
  generalize hDec : ExceptT.run (Fl4Spec.decodePageInvocation slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64SmallPage
      (if mp then some (fa.bv, fv.bv) else none)) ((vc', xsl) :: rest)) σ = D
  unfold vspace.decode_page_map
  rw [hct]
  apply ok_bind_spec
  rw [hex]
  apply ok_bind_spec
  dsimp only
  by_cases h3 : length >= 3#u64
  · rw [if_pos h3]
    have h3' : 3 ≤ args.length := by
      have : 3 ≤ length.val := by scalar_tac
      omega
    obtain ⟨a0, a1, a2, ar', rfl⟩ : ∃ a0 a1 a2 r', args = a0 :: a1 :: a2 :: r' := by
      match args, h3' with
      | a0 :: a1 :: a2 :: r', _ => exact ⟨_, _, _, _, rfl⟩
    rw [hargs 0#u64 a0 (by simp)]; apply ok_bind_spec
    rw [hargs 1#u64 a1 (by simp)]; apply ok_bind_spec
    rw [hargs 2#u64 a2 (by simp)]; apply ok_bind_spec
    unfold lift; apply ok_bind_spec; apply ok_bind_spec; apply ok_bind_spec
    rw [slot_cap_eq, hcx]; apply ok_bind_spec
    by_cases hvp : ∃ p asid, vc = .Pml4 p true asid
    · obtain ⟨p1, as1, rfl⟩ := hvp
      obtain ⟨hp1, has1, has2⟩ := hvc p1 as1 rfl
      have hvc' : vc' = .archObjectCap (.pml4Cap p1.bv (some as1.bv)) := by rw [← hvr.2]; rfl
      subst hvc'
      simp only [vspace.mapped_root, ↓reduceIte, bind_ok]
      cases mp
      · simp only [Bool.false_eq_true, ↓reduceIte, capability.FrameSize.bits, bind_ok, shl12]
        simp only [List.map_cons, Bool.false_eq_true, ↓reduceIte] at hDec
        have hdec0 := decodeMap_unmapped hl a0.bv a1.bv a2.bv (ar'.map UScalar.bv) (pc.bv, idx) dev ptr.bv
          (vmRightsOf rt) .vmNoMap p1.bv as1.bv xsl rest σ
        by_cases hv1 : a0 > fl4_abi.consts.USER_TOP
        · simp only [hv1, ↓reduceIte, error.invalid_arg, bind_ok]
          refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
            Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
          rw [← hDec, hdec0]
          exact runE_bind_err (by rw [runE_whenE_true (Or.inl ((gt_top a0).2 hv1))]; rfl)
        · by_cases hv2 : core.num.U64.wrapping_add a0 4096#u64 > fl4_abi.consts.USER_TOP
          · simp only [hv1, hv2, ↓reduceIte, error.invalid_arg, bind_ok]
            refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
              Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
            rw [← hDec, hdec0]
            exact runE_bind_err (by rw [runE_whenE_true (Or.inr (by rw [← add4096]; exact (gt_top _).2 hv2))]; rfl)
          · simp only [hv1, hv2, ↓reduceIte]
            have hdec : D = ExceptT.run (mapTail p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
              rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false ?_ _ σ)]
              rintro (h | h)
              · exact hv1 ((gt_top a0).1 h)
              · rw [← add4096] at h; exact hv2 ((gt_top _).1 h)
            have hva : a0.val < 2 ^ 48 := by
              have := (show ¬ a0 > fl4_abi.consts.USER_TOP from hv1)
              rw [gt_iff_val] at this
              have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
              omega
            map_tail
      · have hfa := hfm rfl
        have hfa' : (fa != 0#u64) = true := by simp [hfa]
        simp only [↓reduceIte, hfa', capability.FrameSize.bits, bind_ok, shl12]
        simp only [List.map_cons, ↓reduceIte] at hDec
        have hdec0 := decodeMap_mapped hl a0.bv a1.bv a2.bv (ar'.map UScalar.bv) (pc.bv, idx) dev ptr.bv
          (vmRightsOf rt) .vmVSpaceMap fa.bv fv.bv p1.bv as1.bv xsl rest σ
        by_cases hfa1 : fa = as1
        · have : (fa != as1) = false := by simp [hfa1]
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          by_cases hfv : fv = a0
          · have : (fv != a0) = false := by simp [hfv]
            simp only [this, Bool.false_eq_true, ↓reduceIte]
            have hdec : D = ExceptT.run (mapTail p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
              rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
                runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_whenE_false (by simp [hfv]) _ σ)]
            have hva : a0.val < 2 ^ 48 := hfv ▸ hfe.2.2.2
            map_tail
          · have : (fv != a0) = true := by simp [hfv]
            simp only [this, ↓reduceIte, error.invalid_arg, bind_ok]
            refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
              Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
            rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
              runE_bind_ok (runE_whenE_false (by simp) _ σ)]
            exact runE_bind_err (by rw [runE_whenE_true (show fv.bv ≠ a0.bv from fun h => hfv (eq_of_bv h))]; rfl)
        · have : (fa != as1) = true := by simp [hfa1]
          simp only [this, ↓reduceIte, error.invalid_cap, bind_ok]
          refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
          rw [← hDec, hdec0]
          exact runE_bind_err (by rw [runE_whenE_true (show fa.bv ≠ as1.bv from fun h => hfa1 (eq_of_bv h))]; rfl)
    · have hmr : vspace.mapped_root vc = ok none := by
        cases vc <;> simp_all [vspace.mapped_root]
      rw [hmr]
      simp only [bind_ok, error.invalid_cap]
      have hbad : ∀ pm asid, vc' ≠ .archObjectCap (.pml4Cap pm (some asid)) := by
        intro pm asid h
        rw [← hvr.2] at h
        cases vc <;> simp_all [absCap]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
      rw [← hDec, List.map_cons, List.map_cons, List.map_cons]
      exact decodeMap_badVs hl _ _ _ _ _ _ _ _ _ _ _ _ _ hbad σ
  · rw [if_neg h3]
    simp only [error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl, Or.inl (Or.inl (show SysErrRel (.Sys .TruncatedMessage) .truncatedMessage from trivial)),
      hDec ▸ decodeMap_trunc hl _ _ _ _ _ _ _ _ _ ?_ σ, rfl, rfl⟩)
    have : length.val < 3 := by scalar_tac
    simp only [List.length_map]; omega

end

end

end Fl4Proofs.P3.Vs
