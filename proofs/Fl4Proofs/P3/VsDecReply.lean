/-
P3 (DESIGN.md §9), VSpace: **the frame labels that reply inside the
decode** (`TopPostR`/`DecOKR` of HandleTop, as IO port `In` called).

* `decode_invocation_frame_getaddr`: `GetAddress`. FL4 restarts the thread
  and replies the frame's physical address itself; the reply is the named
  hypothesis `GetAddrHyp` (the Ep side: `set_mr`, `set_msg_info`,
  `Running`, against the spec's success tail of `[addrFromPPtr p]`).
* `decode_invocation_frame_tac`: `TestAndClearAccessed`. The decode's
  checks against `decodeTestAndClearAccessed` (`tac_gen`, from VsExtTac's
  lemmas); FL4 then clears the entry's accessed bit and replies whether it
  was set, without a `Restart` first. The reply from the written state is
  the named hypothesis `TacHyp` (the Ep side, as `GetAddrHyp`), against the
  spec's `Restart`, either answer of `performTestAndClearAccessed`, and the
  success tail.
-/
import Fl4Proofs.P3.HandleTop
import Fl4Proofs.P3.VsDecFrame
import Fl4Proofs.P3.VsExtTac
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The `GetAddress` reply** (for the IPC proofs): FL4's `Restart` and
`reply1` of the physical address, against the spec's restart and success
tail of `[addrFromPPtr p]`: FL4 is done, its thread no longer `Restart`,
and the spec has an outcome related to FL4's state. -/
def GetAddrHyp (s : S) (σ : Fl4Spec.State Unit) (ar : A) (ct p : U64) (call : Bool) : Prop :=
  (do
    let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
    let s2 ← vspace.reply1 st s1 ct call (core.num.U64.wrapping_sub p layout.PPTR_BASE)
    ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar)) ⦃ res =>
    res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
      ∃ z ∈ (specTail call ct.bv [Fl4Spec.addrFromPPtr p.bv] σ1).1, RelTopM (L := L) res.2.1 z.2 ⦄

/-- **Frame `GetAddress`** (`DecOKR`, the reply `GetAddrHyp`). -/
theorem decode_invocation_frame_getaddr (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl) (hl : lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) {tcb : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb tcb))
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (slot : U64) (blk call don fp : Bool) (hga : GetAddrHyp (L := L) s σ ar ct p call) (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKRM (L := L) arI s ar σ lbl length slot (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl args ci sl
      excaps buffer ct := by
  subst hl
  unfold DecOKRM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have n1 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageMap; decide
  have n2 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageUnmap; decide
  have n3 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageDeriveSubframe := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageDeriveSubframe; decide
  have n4 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageTestAndClearAccessed := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageTestAndClearAccessed; decide
  have hspec : specDec fp slbl args ci sl (.Frame p sz rt d m false asid va) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          args ci sl (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps)) := by
    show Fl4Spec.NonDetE.liftME _ (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
      (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation frameACapG; dsimp only
    rw [if_neg (fun h => n3 (hlbl.ds h)), if_neg (fun h => n4 (hlbl.tac h))]
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok, n1, n2, hlbl.native, ↓reduceIte]
  rw [hct]; simp only [bind_ok, layout.paddr]
  refine WP.spec_mono hga ?_
  rintro res ⟨h1, hne, hall⟩
  obtain ⟨σ1, hst, -⟩ := setThreadState_eq σ ct.bv tcb hkt .restart
  obtain ⟨z, hz, hRT⟩ := hall σ1 hst
  have hdec := decodeGetAddr_eq (hlbl.ga rfl) args sl d p.bv (vmRightsOf rt) (if m then .vmVSpaceMap else .vmNoMap)
    (frameSizeOf sz) (if m then some (asid.bv, va.bv) else none) excaps σ
  refine Or.inr ⟨h1, hne, _, DecOut.of_eq (run_liftME_ok (run_liftME_ok hdec)), σ1, by rw [hcur]; exact hst,
    [Fl4Spec.addrFromPPtr p.bv], σ1, ?_, z, hz, hRT⟩
  exact mem_liftE (ε := Unit) (x := ([Fl4Spec.addrFromPPtr p.bv], σ1)) rfl


/-- **The `TestAndClearAccessed` reply** (for the IPC proofs): from the
state with the accessed bit of page-table word `b` cleared, FL4's `reply1`
of the answer `v`, against the spec's restart and success tail of `[v]`. -/
def TacHyp (L4 L3 L2 L1 : Set U64) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) (call : Bool) : Prop :=
  ∀ b, PtWAll L4 L3 L2 L1 b → P1.Aligned b → ∀ v : U64, (v = 1#u64 ∨ v = 0#u64) →
    vspace.reply1 st (L.wr s b (L.mem s b &&& ~~~32#u64)) ct call v ⦃ s2 =>
      L.mem s2 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        ∃ z ∈ (specTail call ct.bv [v.bv] σ1).1, RelTopM (L := L) s2 z.2 ⦄

/-- **`TestAndClearAccessed`'s decode checks** against the model's, for any
post `Q`: the errors are the model's; on success, the model's slot, and
FL4 clears the accessed bit of a page-table word and replies 1 or 0. -/
theorem tac_gen [Fl4Proofs.P1.PlainStore st] {P L4 L3 L2 L1 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPP : PtPlaced L4 L3 L2 L1)
    (hPI : PoolsIn P L4 (L.mem s)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (f : vspace.FrameCap) (call : Bool) (Q : core.result.Result Unit error.Exc × S → Prop)
    (herr : ∀ e e', VsErrRel e e' →
      ExceptT.run (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f)) σ = ({(.error e', σ)}, False) →
      Q (.Err e, s))
    (hok : ∀ b, PtWAll L4 L3 L2 L1 b → P1.Aligned b → ∀ slot,
      ExceptT.run (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f)) σ = ({(.ok slot, σ)}, False) →
      ∀ v : U64, (v = 1#u64 ∨ v = 0#u64) →
      vspace.reply1 st (L.wr s b (L.mem s b &&& ~~~32#u64)) ct call v ⦃ s2 => Q (.Ok (), s2) ⦄) :
    vspace.decode_test_and_clear_accessed st s f call ⦃ Q ⦄ := by
  obtain ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩ := f
  generalize hD : ExceptT.run (Fl4Spec.decodeTestAndClearAccessed (Z := Unit)
    (frameACapG ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩)) σ = D
  rw [hD] at herr hok
  unfold vspace.decode_test_and_clear_accessed
  cases sz with
  | Huge =>
    refine WP.spec_bind (Pₘ := fun p => p = (.Huge, true)) (by simp) ?_
    rintro ⟨fs, b⟩ hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    show (if true = true then _ else _) ⦃ _ ⦄
    simp only [↓reduceIte, error.illegal, bind_ok]
    exact (WP.spec_ok _).2 (herr _ .illegalOperation (Or.inl (show SysErrRel (.Sys .IllegalOperation)
      .illegalOperation from trivial)) (hD ▸ decodeTAC_huge _ _ _ _ _ σ))
  | Small =>
    refine WP.spec_bind (Pₘ := fun p => p = (.Small, false)) (by simp) ?_
    rintro ⟨fs, b⟩ hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    show (if false = true then _ else _) ⦃ _ ⦄
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    cases mp
    · simp only [Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (herr _ .illegalOperation (Or.inl (show SysErrRel (.Sys .IllegalOperation)
        .illegalOperation from trivial)) (hD ▸ decodeTAC_unmapped _ _ _ _ (by simp [frameSizeOf]) σ))
    simp only [↓reduceIte]
    by_cases h0 : fa = 0#u64
    · subst h0
      simp only [↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (herr _ .illegalOperation (Or.inl (show SysErrRel (.Sys .IllegalOperation)
        .illegalOperation from trivial)) (hD ▸ decodeTAC_asid0 _ _ _ _ (by simp [frameSizeOf]) _ σ))
    simp only [h0, ↓reduceIte]
    have h0' : fa.bv ≠ 0 := fun h => h0 (P1.eq_of_bv h)
    have hdec := hD.symm.trans (decodeTAC_mapped dev ptr.bv (vmRightsOf rt) .vmVSpaceMap (sz := .x64SmallPage)
      (by decide) h0' fv.bv σ)
    refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR fa h0)
      (find_vspace_for_asid_L4 s σ hR hPI fa)) ?_
    rintro r ⟨hf, hL⟩
    cases r with
    | Err lf =>
      simp only [error.invalid_cap, bind_ok]
      exact (WP.spec_ok _).2 (herr _ (.invalidCapability 0) (Or.inr ⟨0#u64, rfl, rfl⟩) (hdec.trans (fms_noVs hf)))
    | Ok r1 =>
      have hr1 := hL r1 rfl
      dsimp only
      refine WP.spec_bind (mapped_entry_small s σ hPt hPP hr1 ptr rt fa fv dev true hf) ?_
      rintro o hme
      rcases hme with ⟨rfl, hfms⟩ | ⟨q, hq, rfl, hfms⟩
      · simp only [error.invalid_cap, bind_ok]
        exact (WP.spec_ok _).2 (herr _ (.invalidCapability 0) (Or.inr ⟨0#u64, rfl, rfl⟩) (hdec.trans hfms))
      dsimp only
      rw [hct]
      apply Endp.ok_bind_spec
      rw [L.read_eq]
      apply Endp.ok_bind_spec
      rw [P_ACCESSED_eq]
      apply Endp.ok_bind_spec
      unfold lift
      apply Endp.ok_bind_spec
      apply Endp.ok_bind_spec
      rw [L.write_eq]
      apply Endp.ok_bind_spec
      apply Endp.ok_bind_spec
      have hqa := hPP q (Or.inr (Or.inr (Or.inr hq)))
      have hj := vIdx_lt fv 12
      have hea : P1.Aligned (peA q (vIdx fv 12)) := by
        show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
      have hb : PtWAll L4 L3 L2 L1 (peA q (vIdx fv 12)) := ⟨q, Or.inr (Or.inr (Or.inr hq)), _, hj, rfl⟩
      split
      · refine WP.spec_bind (hok _ hb hea _ (hdec.trans hfms) 1#u64 (Or.inl rfl)) ?_
        rintro s2 h
        exact (WP.spec_ok _).2 h
      · refine WP.spec_bind (hok _ hb hea _ (hdec.trans hfms) 0#u64 (Or.inr rfl)) ?_
        rintro s2 h
        exact (WP.spec_ok _).2 h
  | Large =>
    refine WP.spec_bind (Pₘ := fun p => p = (.Large, false)) (by simp) ?_
    rintro ⟨fs, b⟩ hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    show (if false = true then _ else _) ⦃ _ ⦄
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    cases mp
    · simp only [Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (herr _ .illegalOperation (Or.inl (show SysErrRel (.Sys .IllegalOperation)
        .illegalOperation from trivial)) (hD ▸ decodeTAC_unmapped _ _ _ _ (by simp [frameSizeOf]) σ))
    simp only [↓reduceIte]
    by_cases h0 : fa = 0#u64
    · subst h0
      simp only [↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (herr _ .illegalOperation (Or.inl (show SysErrRel (.Sys .IllegalOperation)
        .illegalOperation from trivial)) (hD ▸ decodeTAC_asid0 _ _ _ _ (by simp [frameSizeOf]) _ σ))
    simp only [h0, ↓reduceIte]
    have h0' : fa.bv ≠ 0 := fun h => h0 (P1.eq_of_bv h)
    have hdec := hD.symm.trans (decodeTAC_mapped dev ptr.bv (vmRightsOf rt) .vmVSpaceMap (sz := .x64LargePage)
      (by decide) h0' fv.bv σ)
    refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR fa h0)
      (find_vspace_for_asid_L4 s σ hR hPI fa)) ?_
    rintro r ⟨hf, hL⟩
    cases r with
    | Err lf =>
      simp only [error.invalid_cap, bind_ok]
      exact (WP.spec_ok _).2 (herr _ (.invalidCapability 0) (Or.inr ⟨0#u64, rfl, rfl⟩) (hdec.trans (fms_noVs hf)))
    | Ok r1 =>
      have hr1 := hL r1 rfl
      dsimp only
      refine WP.spec_bind (mapped_entry_large s σ hPt hPP hr1 ptr rt fa fv dev true hf) ?_
      rintro o hme
      rcases hme with ⟨rfl, hfms⟩ | ⟨q, hq, rfl, hfms⟩
      · simp only [error.invalid_cap, bind_ok]
        exact (WP.spec_ok _).2 (herr _ (.invalidCapability 0) (Or.inr ⟨0#u64, rfl, rfl⟩) (hdec.trans hfms))
      dsimp only
      rw [hct]
      apply Endp.ok_bind_spec
      rw [L.read_eq]
      apply Endp.ok_bind_spec
      rw [P_ACCESSED_eq]
      apply Endp.ok_bind_spec
      unfold lift
      apply Endp.ok_bind_spec
      apply Endp.ok_bind_spec
      rw [L.write_eq]
      apply Endp.ok_bind_spec
      apply Endp.ok_bind_spec
      have hqa := hPP q (Or.inr (Or.inr (Or.inl hq)))
      have hj := vIdx_lt fv 21
      have hea : P1.Aligned (peA q (vIdx fv 21)) := by
        show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
      have hb : PtWAll L4 L3 L2 L1 (peA q (vIdx fv 21)) := ⟨q, Or.inr (Or.inr (Or.inl hq)), _, hj, rfl⟩
      split
      · refine WP.spec_bind (hok _ hb hea _ (hdec.trans hfms) 1#u64 (Or.inl rfl)) ?_
        rintro s2 h
        exact (WP.spec_ok _).2 h
      · refine WP.spec_bind (hok _ hb hea _ (hdec.trans hfms) 0#u64 (Or.inr rfl)) ?_
        rintro s2 h
        exact (WP.spec_ok _).2 h

/-- **Frame `TestAndClearAccessed`** (`DecOKR`, the reply `TacHyp`). -/
theorem decode_invocation_frame_tac [Fl4Proofs.P1.PlainStore st] {P L4 L3 L2 L1 : Set U64} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPP : PtPlaced L4 L3 L2 L1)
    (hPI : PoolsIn P L4 (L.mem s))
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hl : lbl = fl4_abi.label.X86PageTestAndClearAccessed)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) {tcb : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb tcb))
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (slot : U64) (blk call don fp : Bool) (htac : TacHyp (L := L) L4 L3 L2 L1 s σ ct call)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKRM (L := L) arI s ar σ lbl length slot (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl args ci sl
      excaps buffer ct := by
  subst hl
  unfold DecOKRM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have n1 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageMap; decide
  have n2 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageUnmap; decide
  have n3 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageGetAddress := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageGetAddress; decide
  have n4 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageDeriveSubframe := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageDeriveSubframe; decide
  set f : vspace.FrameCap := ⟨p, sz, rt, d, m, false, asid, va⟩ with hfdef
  have hspec : specDec fp slbl args ci sl (.Frame p sz rt d m false asid va) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.testAndClearAccessed
          (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f))) := by
    show Fl4Spec.NonDetE.liftME _ (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
      (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation frameACapG; dsimp only
    rw [if_neg (fun h => n4 (hlbl.ds h)), if_pos (hlbl.tacr rfl)]
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  have hfc : vspace.as_frame (.Frame p sz rt d m false asid va) = ok (some f) := rfl
  rw [hfc]
  simp only [bind_ok, n1, n2, n3, hlbl.native, ↓reduceIte]
  obtain ⟨σ1, hst, -⟩ := setThreadState_eq σ ct.bv tcb hkt .restart
  refine WP.spec_bind (tac_gen (L := L) s σ hR hPt hPP hPI ct hct f call
    (fun r => TopPostRM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.testAndClearAccessed
          (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f)))) ct s (r.1, r.2, ar))
    (fun e e' hE hDe => Or.inl ⟨e, rfl, rfl, e', run_liftME_err (run_liftME_err hDe), hE⟩)
    (fun b hb hal slot' hDs v hv => by
      refine WP.spec_mono (htac b hb hal v hv) ?_
      rintro s2 ⟨hne, hall⟩
      obtain ⟨z, hz, hRT⟩ := hall σ1 hst
      have hsel : ([v.bv], σ1) ∈ (Fl4Spec.performTestAndClearAccessed (Z := Unit) slot' σ1).1 := by
        simp only [Fl4Spec.performTestAndClearAccessed, Fl4Spec.NonDet.select, Set.mem_setOf_eq,
          Set.mem_insert_iff, Set.mem_singleton_iff, and_true]
        rcases hv with rfl | rfl
        · right; rfl
        · left; rfl
      exact Or.inr ⟨rfl, hne, _, DecOut.of_eq (run_liftME_ok (run_liftME_ok hDs)), σ1, by rw [hcur]; exact hst,
        [v.bv], σ1, mem_liftE (ε := Unit) (x := ([v.bv], σ1)) hsel, z, hz, hRT⟩)) ?_
  rintro ⟨r, s1⟩ h
  exact (WP.spec_ok _).2 h




/-! ## With an extra relation on the outcome -/

/-- **`TopPostRM` with an extra relation `X`** on the outcome (`σ` on an
error, the success tail's state on success). -/
def TopPostRMX (X : S → A → Fl4Spec.State Unit → Prop) (σ : Fl4Spec.State Unit) (blk call don : Bool)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) (ct : U64) (s : S)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ (∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∧
    X res.2.1 res.2.2 σ) ∨
  res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧
  ∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1 ∧
      ∃ z ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) res.2.1 z.2 ∧ X res.2.1 res.2.2 z.2

theorem TopPostRMX.toRM {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} (h : TopPostRMX (L := L) X σ blk call don m ct s res) :
    TopPostRM (L := L) σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3, -⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, -⟩
  · exact Or.inl ⟨e, h1, h2, h3⟩
  · exact Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6⟩

/-- **`DecOKRM` with `X` on the outcome.** -/
abbrev DecOKRMX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostRMX (L := L) X σ blk call don (specDec fp slbl args ci sl c excaps buffer) ct s res ⦄

theorem DecOKRMX.toRM {X : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : DecOKRMX (L := L) arI X s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct) :
    DecOKRM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct :=
  WP.spec_mono h fun _ h => h.toRM

/-- **`GetAddrHyp` keeping `X`**: from a state with `X`, the reply's outcome
has `X` too (with the spec's tail state). -/
def GetAddrHypX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (σ : Fl4Spec.State Unit) (ar : A) (ct p : U64)
    (call : Bool) : Prop :=
  X s ar σ → (do
    let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
    let s2 ← vspace.reply1 st s1 ct call (core.num.U64.wrapping_sub p layout.PPTR_BASE)
    ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar)) ⦃ res =>
    res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
      ∃ z ∈ (specTail call ct.bv [Fl4Spec.addrFromPPtr p.bv] σ1).1, RelTopM (L := L) res.2.1 z.2 ∧
        X res.2.1 res.2.2 z.2 ⦄

/-- **`TacHyp` keeping `X`**: from the state with the accessed bit cleared,
with `X` there, the reply's outcome has `X` too. -/
def TacHypX (X : S → A → Fl4Spec.State Unit → Prop) (L4 L3 L2 L1 : Set U64) (s : S) (σ : Fl4Spec.State Unit)
    (ar : A) (ct : U64) (call : Bool) : Prop :=
  ∀ b, PtWAll L4 L3 L2 L1 b → P1.Aligned b → ∀ v : U64, (v = 1#u64 ∨ v = 0#u64) →
    X (L.wr s b (L.mem s b &&& ~~~32#u64)) ar σ →
    vspace.reply1 st (L.wr s b (L.mem s b &&& ~~~32#u64)) ct call v ⦃ s2 =>
      L.mem s2 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        ∃ z ∈ (specTail call ct.bv [v.bv] σ1).1, RelTopM (L := L) s2 z.2 ∧ X s2 ar z.2 ⦄

/-- **Frame `GetAddress` keeping `X`** (`DecOKRMX`, the reply `GetAddrHypX`). -/
theorem decode_invocation_frame_getaddrX {X : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl) (hl : lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) {tcb : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb tcb))
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (slot : U64) (blk call don fp : Bool) (hga : GetAddrHypX (L := L) X s σ ar ct p call) (hX0 : X s ar σ) (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKRMX (L := L) arI X s ar σ lbl length slot (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl args ci sl
      excaps buffer ct := by
  subst hl
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have n1 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageMap; decide
  have n2 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageUnmap; decide
  have n3 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageDeriveSubframe := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageDeriveSubframe; decide
  have n4 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageTestAndClearAccessed := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageTestAndClearAccessed; decide
  have hspec : specDec fp slbl args ci sl (.Frame p sz rt d m false asid va) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          args ci sl (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps)) := by
    show Fl4Spec.NonDetE.liftME _ (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
      (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation frameACapG; dsimp only
    rw [if_neg (fun h => n3 (hlbl.ds h)), if_neg (fun h => n4 (hlbl.tac h))]
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok, n1, n2, hlbl.native, ↓reduceIte]
  rw [hct]; simp only [bind_ok, layout.paddr]
  refine WP.spec_mono (hga hX0) ?_
  rintro res ⟨h1, hne, hall⟩
  obtain ⟨σ1, hst, -⟩ := setThreadState_eq σ ct.bv tcb hkt .restart
  obtain ⟨z, hz, hRT, hXz⟩ := hall σ1 hst
  have hdec := decodeGetAddr_eq (hlbl.ga rfl) args sl d p.bv (vmRightsOf rt) (if m then .vmVSpaceMap else .vmNoMap)
    (frameSizeOf sz) (if m then some (asid.bv, va.bv) else none) excaps σ
  refine Or.inr ⟨h1, hne, _, DecOut.of_eq (run_liftME_ok (run_liftME_ok hdec)), σ1, by rw [hcur]; exact hst,
    [Fl4Spec.addrFromPPtr p.bv], σ1, ?_, z, hz, hRT, hXz⟩
  exact mem_liftE (ε := Unit) (x := ([Fl4Spec.addrFromPPtr p.bv], σ1)) rfl

/-- **Frame `TestAndClearAccessed` keeping `X`** (`DecOKRMX`, the reply `TacHypX`; `X` after the
accessed-bit clear given). -/
theorem decode_invocation_frame_tacX [Fl4Proofs.P1.PlainStore st] {X : S → A → Fl4Spec.State Unit → Prop} {P L4 L3 L2 L1 : Set U64} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPP : PtPlaced L4 L3 L2 L1)
    (hPI : PoolsIn P L4 (L.mem s))
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hl : lbl = fl4_abi.label.X86PageTestAndClearAccessed)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) {tcb : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb tcb))
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (slot : U64) (blk call don fp : Bool) (htac : TacHypX (L := L) X L4 L3 L2 L1 s σ ar ct call) (hX0 : X s ar σ)
    (hXc : ∀ b, PtWAll L4 L3 L2 L1 b → P1.Aligned b → X (L.wr s b (L.mem s b &&& ~~~32#u64)) ar σ)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKRMX (L := L) arI X s ar σ lbl length slot (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl args ci sl
      excaps buffer ct := by
  subst hl
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have n1 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageMap; decide
  have n2 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageUnmap; decide
  have n3 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageGetAddress := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageGetAddress; decide
  have n4 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageDeriveSubframe := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageDeriveSubframe; decide
  set f : vspace.FrameCap := ⟨p, sz, rt, d, m, false, asid, va⟩ with hfdef
  have hspec : specDec fp slbl args ci sl (.Frame p sz rt d m false asid va) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.testAndClearAccessed
          (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f))) := by
    show Fl4Spec.NonDetE.liftME _ (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
      (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation frameACapG; dsimp only
    rw [if_neg (fun h => n4 (hlbl.ds h)), if_pos (hlbl.tacr rfl)]
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  have hfc : vspace.as_frame (.Frame p sz rt d m false asid va) = ok (some f) := rfl
  rw [hfc]
  simp only [bind_ok, n1, n2, n3, hlbl.native, ↓reduceIte]
  obtain ⟨σ1, hst, -⟩ := setThreadState_eq σ ct.bv tcb hkt .restart
  refine WP.spec_bind (tac_gen (L := L) s σ hR hPt hPP hPI ct hct f call
    (fun r => TopPostRMX (L := L) X σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.testAndClearAccessed
          (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f)))) ct s (r.1, r.2, ar))
    (fun e e' hE hDe => Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err (run_liftME_err hDe), hE⟩, hX0⟩)
    (fun b hb hal slot' hDs v hv => by
      refine WP.spec_mono (htac b hb hal v hv (hXc b hb hal)) ?_
      rintro s2 ⟨hne, hall⟩
      obtain ⟨z, hz, hRT, hXz⟩ := hall σ1 hst
      have hsel : ([v.bv], σ1) ∈ (Fl4Spec.performTestAndClearAccessed (Z := Unit) slot' σ1).1 := by
        simp only [Fl4Spec.performTestAndClearAccessed, Fl4Spec.NonDet.select, Set.mem_setOf_eq,
          Set.mem_insert_iff, Set.mem_singleton_iff, and_true]
        rcases hv with rfl | rfl
        · right; rfl
        · left; rfl
      exact Or.inr ⟨rfl, hne, _, DecOut.of_eq (run_liftME_ok (run_liftME_ok hDs)), σ1, by rw [hcur]; exact hst,
        [v.bv], σ1, mem_liftE (ε := Unit) (x := ([v.bv], σ1)) hsel, z, hz, hRT, hXz⟩)) ?_
  rintro ⟨r, s1⟩ h
  exact (WP.spec_ok _).2 h

end

end

end Fl4Proofs.P3
