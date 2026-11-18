/-
P3 (DESIGN.md §9), CSpace: **the deletion at `XTop`** by the W-threading
(DelW): the invariant `WX` (`XTopAt` at sets of the typed heap with the ghost
tree, `KsApart`, the typed heap's TCBs among the sets') carried through
CNode Delete and Revoke.

* `slotHypW_X`: the deletion's slot edits keep `WX` (`XTopAt.slotStepT`,
  `CurOK` after from the MDB's VSpace invariant, `CurOK.of_inv'`).
* `finObjHypW_X`: the object finalisations at `WX`, from `XFinHyps`
  (the finalisations that do work) and `fin_idle` (the others).
* `ppHypDW_X`: the preemption points at `WX`, from `XPreemptHyp`.
* `XPostDelHyp`, `postDelHypW_X`: `post_cap_deletion` at `XTop` (a named
  premise in the `XTopAt` shape) and `PostDelHypW` from it.
* `delHypsW_X`: the four bundled.
-/
import Fl4Proofs.P3.XTopCnode
import Fl4Proofs.P3.XTopDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The deletion's invariant at `XTop`**: `XTopAt` at sets of the typed
heap `th` with the ghost tree `G`, the IPC objects outside the kernel-global
block, the typed heap's TCBs among the sets'. -/
def WX (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) :
    Prop :=
  ∃ Z : XSets, Z.th = th ∧ Z.G = G ∧ XTopAt (L := L) AR Z s a σ ∧ KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
    ∀ t, th t = some .tcb → t ∈ Z.T

theorem WX.of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) : WX (L := L) AR Z.th s a σ Z.G :=
  ⟨Z, rfl, rfl, hX, hK, hTh⟩

/-- Slot words only, as `WritesIn` of the slot words. -/
theorem SlotFrame2.writesIn {th : TypedHeap} {s s' : S} (h : SlotFrame2 (L := L) th s s') :
    P1.WritesIn st s s' (Sched.SlotWd th) :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun ⟨y, k, hy, hk, e⟩ => hn ⟨y, hy, k, hk, e⟩⟩

/-- **The deletion's slot edits keep `WX`.** -/
theorem slotHypW_X (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) :
    SlotHypW (L := L) (A := A) (WX (L := L) AR th) th := by
  rintro s s' a σ σ' G G' ⟨Z, rfl, rfl, hX, hK, hTh⟩ - ⟨hCR', -, hFI'⟩ hF hcn hSt
  have hMO := hSt.okv hX.rel.2.2.2.2.1
  have hct : σ'.curThread = σ.curThread := by have e := congrArg Fl4Spec.AbstractState.curThread hcn.1; exact e
  have hCO := CurOK.of_inv' hX.fin.2.2.2.2 hct hCR'.2.2.1 hMO.2.2
  exact ⟨{ Z with G := G' }, rfl, rfl, XTopAt.slotStepT hX (SlotFrame2.writesIn hF) hcn hCR' hFI' hMO hCO,
    by rw [hF.1]; exact hK, hTh⟩

/-- **The object finalisations at `WX`**: those doing work from
`XFinHyps`, the others leave the state as it is (`fin_idle`). -/
theorem finObjHypW_X [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hXF : XFinHyps (L := L) arI AR th) :
    FinObjHypW (L := L) arI (WX (L := L) AR th) th := by
  rintro s a σ G sl c hDS ⟨Z, rfl, rfl, hX, hK, hTh⟩ hA hc hk
  by_cases hw : FinWork c (decide (Fl4Spec.isFinalCap' (absCap c) σ))
  · refine WP.spec_mono (hXF.at arI Z s a σ sl c rfl hX hK hTh trivial hDS hA hc hk hw) ?_
    rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, ⟨V', hX'⟩, hk'⟩
    refine ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, Z.mv G' V', rfl, rfl, hX', by rw [hk']; exact hK, hTh⟩
  obtain ⟨cl, he, hmem, hcl, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c hk _ hw
  rw [he, WP.spec_ok]
  have hcw : CapWf c := by
    obtain ⟨c', a', hc', hca, -⟩ := hDS.1.1.abs_cap hA
    rw [hc] at hc'; cases eq_of_ok_eq hc'; exact hca.1
  refine ⟨hrem.symm, ?_, ?_, σ, Z.G, hmem, hDS, capV_of_capAt hc, fun _ _ _ => Or.inl rfl,
    MdbStep.refl hDS.1.2.2.1, Z, rfl, rfl, hX, hK, hTh⟩
  · rcases hcl with h | h
    · rw [h]; trivial
    · by_cases hio : ∃ f l, c = .IoPort f l 0#u64
      · obtain ⟨f, l, rfl⟩ := hio; rw [h]; trivial
      · rw [hnio (fun f l e => hio ⟨f, l, e⟩)]; trivial
  · rcases hcl with h | h
    · rw [h]; trivial
    · rw [h]; exact hcw

/-- **The preemption points at `WX`**, from `XPreemptHyp`. -/
theorem ppHypDW_X {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hXP : XPreemptHyp (L := L) arI AR th) :
    PPHypDW (L := L) arI (WX (L := L) AR th) (WX (L := L) AR th) th := by
  rintro s a σ G - ⟨Z, rfl, rfl, hX, hK, hTh⟩
  refine WP.spec_mono (hXP.pp arI rfl hX hK hTh) ?_
  rintro r ⟨hS, σ', hcase, hCR, hX', hk'⟩
  exact ⟨hS, σ', hcase, hCR, WPost_self.2 ⟨Z, rfl, rfl, hX', by rw [hk']; exact hK, hTh⟩⟩

/-- **Hypothesis: `post_cap_deletion` at `XTop`** (an IRQ handler's or an IO
port's cleanup, kernel-state words and the arch state; `XTopAt.ksStep`'s
shape): from `XTopAt` with `DState`, the cap slots and the kernel-global
base kept, a spec outcome, the CSpace relation and `XTopAt` after at the
same sets. -/
def XPostDelHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (s : S) (a : A) (σ : Fl4Spec.State Unit) (cl : capability.Cap),
    Z.th = th → XTopAt (L := L) AR Z s a σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) →
    (∀ t, th t = some .tcb → t ∈ Z.T) → DState (L := L) th s σ Z.G →
    CleanCap cl → cl ≠ .Null → CapWf cl →
    objects.post_cap_deletion st arI s a cl ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.1) ∧ L.ksb r.1 = L.ksb s ∧ ∃ σ',
        ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap cl) σ).1 ∧ CRel th (L.mem r.1) σ' Z.G ∧
        XTopAt (L := L) AR Z r.1 r.2 σ' ⦄

theorem postDelHypW_X {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hXD : XPostDelHyp (L := L) arI AR th) :
    PostDelHypW (L := L) arI (WX (L := L) AR th) th := by
  rintro s a σ G cl hDS ⟨Z, rfl, rfl, hX, hK, hTh⟩ h1 h2 h3
  refine WP.spec_mono (hXD Z s a σ cl rfl hX hK hTh hDS h1 h2 h3) ?_
  rintro r ⟨hS, hk', σ', hm, hCR, hX'⟩
  exact ⟨hS, σ', hm, hCR, Z, rfl, rfl, hX', by rw [hk']; exact hK, hTh⟩

/-- **The deletion's premises at `WX`.** -/
theorem delHypsW_X [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hXF : XFinHyps (L := L) arI AR th)
    (hXP : XPreemptHyp (L := L) arI AR th) (hXD : XPostDelHyp (L := L) arI AR th) :
    DelHypsW (L := L) arI (WX (L := L) AR th) th :=
  ⟨finObjHypW_X arI hXF, ppHypDW_X arI hXP, postDelHypW_X arI hXD, slotHypW_X AR th⟩

/-! ## CNode Delete and Revoke at `XTop` -/

/-- The invariant of the CNode deletes at `XTop`: `DelE` (the deletion's
CSpace invariant and fuel bound) and `WX`. -/
abbrev EX (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (K : Nat) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) : Prop :=
  DelE (L := L) th K s σ ∧ WX (L := L) AR th s a σ G

set_option maxHeartbeats 4000000 in
/-- **A Delete's or Revoke's outcome at `XTop`**: from `PInvPostW` at `EX`,
`TopPostDMX` (done or preempted, `XTop` after). -/
theorem cn_del_topX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s ar σ) {K : Nat} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : PInvPostW (L := L) Z.th σ Z.G m (EX (L := L) AR Z.th K) (EX (L := L) AR Z.th K) s ar res) :
    TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m)
      s res := by
  obtain ⟨r, s', a'⟩ := res
  rcases hq with ⟨e, rfl, rfl, rfl, e', h1, h2⟩ | ⟨inv, hrun, σ1, hst, σ', G', hcase, -, -, -, hE'⟩
  · exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, hX⟩⟩
  · obtain ⟨-, Z', -, -, hX', -, -⟩ := WPost_self.1 hE'
    rcases hcase with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ⟨Z', hX'⟩⟩
    · exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.error (), σ'),
        mem_bindE_err hx, ⟨Z'.th, Z'.G, Or.inr ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ⟨Z', hX'⟩⟩

/-- `EX` after the caller's restart. -/
theorem EX.restart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {K : Nat}
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDE : DelE (L := L) Z.th K s σ) {ct : U64}
    (hcur : σ.curThread = ct.bv) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame Z.th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      EX (L := L) AR Z.th K s1 ar σ1 Z.G := by
  intro s1 σ1 hs1 hS hst
  have hst' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by rw [← hcur]; exact hst
  obtain ⟨hX1, hk1, -⟩ := hX.restart' hC hcur hs1 hst'
  exact ⟨delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) hst),
    Z, rfl, rfl, hX1, by rw [hk1]; exact hKA, hTh⟩

/-- **`CnodeXHyp` at the Revoke label** (25), the deletes of the children
and the preemption points at `XTop`: `cnode_revoke_refinesW` at `EX`
(`delHyp_fullW`, `rppHyp_fullW` from `delHypsW_X`), then `cn_del_topX`.
Beyond `decode_invocation_cnode_otherX`'s premises: the deletion's
premises at `XTop` (`XFinHyps`, `XPreemptHyp`, `XPostDelHyp`), `KsApart`,
the typed heap's TCBs in `Z.T`, the bound `K` on CNode sizes and `DelE`. -/
theorem decode_invocation_cnode_revokeX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th)
    (K : Nat) (hK : ∀ p r, Z.th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K) (hDE : DelE (L := L) Z.th K s σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.CNodeRevoke length slot (.CNode p r gs g) blk call don
      fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  have hH := delHypsW_X arI hXF hXP hXD
  have hfew : psiD (L.mem s) Z.G < 2 ^ 64 - 1 := by
    have := hDE.2.1 Z.G hM
    have : psiD (L.mem s) Z.G ≤ psiD (L.mem s) Z.G * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_revoke_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI hact hcur htcb (EX (L := L) AR Z.th K) (EX (L := L) AR Z.th K)
      psiD psiD_slotsSame
      (delHyp_fullW arI (WX (L := L) AR Z.th) Z.th hP (finalHyp_full Z.th hP) hH K hK hK6)
      (rppHyp_fullW arI (WX (L := L) AR Z.th) (WX (L := L) AR Z.th) Z.th K hH.pp) (EX.restart hX hKA hC hTh hDE hcur)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩) hfew)
      fun res h => cn_del_topX hX h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩

/-- **`CnodeXHyp` at the Delete label** (26), for any cap: as
`decode_invocation_cnode_revokeX`, by `cnode_delete_refinesW` at `EX`. -/
theorem decode_invocation_cnode_deleteX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th)
    (K : Nat) (hK : ∀ p r, Z.th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K) (hDE : DelE (L := L) Z.th K s σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.CNodeDelete length slot (.CNode p r gs g) blk call don
      fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  have hH := delHypsW_X arI hXF hXP hXD
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_delete_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI hact hcur htcb (EX (L := L) AR Z.th K) (EX (L := L) AR Z.th K) psiD
      (delHyp_fullW arI (WX (L := L) AR Z.th) Z.th hP (finalHyp_full Z.th hP) hH K hK hK6)
      (EX.restart hX hKA hC hTh hDE hcur)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩))
      fun res h => cn_del_topX hX h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩

end

end

end Fl4Proofs.P3
