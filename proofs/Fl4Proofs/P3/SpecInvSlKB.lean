/-
P3 (DESIGN.md §9), invariant line G1 (sl5): **`KS σ0` across the CNode, IRQ and
TCB performs and the IPC cap transfer** (spec side only; sl4 handoff 2, the cap
writers of the performs; SpecInvSlKA).

* `KCn σ0` (CNode insert / move / rotate caps `KOk σ0`, from the decode,
  SpecInvSlKD) and `ks_invokeCnode`; delete / revoke by SpecInvSlKA.
* IRQ control and the arch / FL4 IRQ issue paths write IRQ handler caps (empty
  range, `kok_irqH`): no hypothesis. `KIh σ0` (the set-handler cap `KOk σ0`) and
  `ks_invokeIrqHandler`.
* TCB installs re-read the source slot (`check_cap_at`): **`kd_of_so`**
  (`same_object_as nc c'` makes `nc` `KD` to the slot cap `c'`: same SC-ness, the
  object, a frame of the same base and size), so `ks_installTcbCap`,
  `ks_installTcbFrameCap`, **`ks_invokeTcb`** need no decode fact.
* IPC: `kd_deriveCap` (a derived cap is `KD` to its source), `ks_transferCapsLoop`
  (caps `KOk σ0`), `ks_transferCaps`, **`ks_doNormalTransfer : KK`** (the extra caps
  are looked up in the same transfer: slot caps of a `KS σ0` state).
-/
import Fl4Proofs.P3.SpecInvSlKA
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
open Fl4Proofs.P3.SInvV (hV hV_cap WLH)
open Fl4Proofs.P3.SInvDom (OkDAt okdAt_bind okdAt_returnOk okdAt_throw okdAt_ite okdAt_liftME okdAt_returnOk_bind okdAt_whenE_bind)

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## CNode -/

/-- The caps a CNode invocation writes are `KOk σ0`. -/
def KCn (σ0 : State Unit) : CnodeInvocation → Prop
  | .insertCall cap _ _ => KOk σ0 cap
  | .moveCall cap _ _ => KOk σ0 cap
  | .rotateCall c1 c2 _ _ _ => KOk σ0 c1 ∧ KOk σ0 c2
  | _ => True

theorem ks_invokeCnode {σ0 : State Unit} (i : CnodeInvocation) (h : KCn σ0 i) :
    IKE (KS σ0) (invokeCnode (Z := Unit) i) := by
  cases i with
  | revokeCall sl => unfold invokeCnode; exact ks_capRevoke sl σ0
  | deleteCall sl => unfold invokeCnode; exact ks_capDelete sl σ0
  | insertCall cap src dest => unfold invokeCnode withoutPreemption; exact ike_liftE (ks_capInsert src dest h)
  | moveCall cap src dest => unfold invokeCnode withoutPreemption; exact ike_liftE (ks_capMove src dest h)
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨k1, k2⟩ := h
    unfold invokeCnode withoutPreemption
    refine ike_liftE ?_
    split
    · rename_i e; subst e; exact ks_capSwap _ _ k2 k1
    · exact ik_bind (ks_capMove _ _ k2) fun _ => ks_capMove _ _ k1
  | cancelBadgedSendsCall cap =>
    unfold invokeCnode withoutPreemption
    split <;> (try (rename_i heq; cases heq; done))
    all_goals first
      | exact ike_liftE (ik_when _ (SInvV.hv_cancelBadgedSends (P := KS σ0) _ _))
      | exact ike_liftE ik_fail

/-! ## IRQ control and handlers -/

theorem kok_irqH {σ0 : State Unit} (i : Irq) : KOk σ0 (.irqHandlerCap i) :=
  kok_empty (by ext r; simp [capRng, objRefs]) (fun _ _ e => by cases e)

theorem ks_invokeIrqControl {σ0 : State Unit} (i : IrqControlInvocation) :
    IKE (KS σ0) (invokeIrqControl (Z := Unit) i) := by
  cases i with
  | irqControl irq hs cs =>
    unfold invokeIrqControl
    exact ike_liftE (ik_bind (ks_setIrqState _ _) fun _ => ks_capInsert _ _ (kok_irqH _))
  | archIRQControl a =>
    unfold invokeIrqControl archInvokeIrqControl withoutPreemption
    cases a with
    | issueIRQHandlerIOAPIC irq dest src io pin lv pol vec =>
      refine ike_liftE ?_
      refine ik_bind (ks_doMachineOp _) fun _ => ik_pure_bind ?_
      refine ik_bind (SInvV.hv_updateIrqState _ _) fun _ => ik_bind (ks_setIrqState _ _) fun _ => ?_
      exact ks_capInsert _ _ (kok_irqH _)
    | issueIRQHandlerMSI irq dest src bus dev func hd =>
      refine ike_liftE ?_
      refine ik_pure_bind ?_
      refine ik_bind (SInvV.hv_updateIrqState _ _) fun _ => ik_bind (ks_setIrqState _ _) fun _ => ?_
      exact ks_capInsert _ _ (kok_irqH _)

theorem ks_invokeFl4IrqControl {σ0 : State Unit} (i : Fl4IrqControlInvocation) :
    IKE (KS σ0) (invokeFl4IrqControl (Z := Unit) i) := by
  cases i with
  | spec i => unfold invokeFl4IrqControl; exact ks_invokeIrqControl i
  | ioapicRemapped irq dest src io pin lv pol vec hd =>
    unfold invokeFl4IrqControl withoutPreemption
    refine ike_liftE ?_
    refine ik_bind (ks_doMachineOp _) fun _ => ik_pure_bind ?_
    refine ik_bind (SInvV.hv_updateIrqState _ _) fun _ => ik_bind (ks_setIrqState _ _) fun _ => ?_
    exact ks_capInsert _ _ (kok_irqH _)

/-- The set-handler cap is `KOk σ0` (it is read from a slot by the decode). -/
def KIh (σ0 : State Unit) : IrqHandlerInvocation → Prop
  | .setIRQHandler _ c _ => KOk σ0 c
  | _ => True

theorem ks_invokeIrqHandler {σ0 : State Unit} (i : IrqHandlerInvocation) (h : KIh σ0 i) :
    IK (KS σ0) (invokeIrqHandler (Z := Unit) i) := by
  cases i with
  | aCKIrq irq => unfold invokeIrqHandler archInvokeIrqHandler; exact ks_doMachineOp _
  | setIRQHandler irq cap sl =>
    unfold invokeIrqHandler getIrqSlot
    refine ik_gets_bind fun σ => ikp_of_ik ?_ σ
    exact ik_bind (ks_capDeleteOne _ σ0) fun _ => ks_capInsert _ _ h
  | clearIRQHandler irq =>
    unfold invokeIrqHandler
    exact ik_bind (SInvV.hv_getIrqSlot _) fun _ => ks_capDeleteOne _ σ0

/-! ## TCB -/

/-- **`same_object_as nc c'`** makes `nc` derived from `c'`. -/
theorem kd_of_so {nc c' : Cap} (h : sameObjectAs nc c') : KD c' nc := by
  obtain ⟨hr, h1, h2, -, -⟩ := so_facts h
  refine ⟨h1, fun r hr' => ?_⟩
  by_cases hs : ∃ b, c' = .schedContextCap r b
  · obtain ⟨b, e⟩ := hs; exact Or.inl (h2 r b e)
  · refine Or.inr ⟨?_, fun b e => hs ⟨b, e⟩⟩
    cases nc with
    | archObjectCap a =>
      cases c' with
      | archObjectCap a' =>
        simp only [sameObjectAs] at h
        simp only [capRng] at hr' ⊢
        cases a <;> cases a' <;> simp_all [sameAobjectAs, archSameRegionAs, acRng, aobjRef]
      | _ => simp [sameObjectAs, sameRegionAs] at h
    | _ => exact objRefs_sub_capRng _ (hr r (by simpa [capRng] using hr'))

/-- `check_cap_at newCap src (check_cap_at (ThreadCap t) sl (cap_insert newCap src dst))`:
the re-read source cap makes `newCap` `KOk`. -/
theorem ks_checkCapAt_ins {σ0 : State Unit} (nc : Cap) (src : CslotPtr) (t : ObjRef) (sl dst : CslotPtr) :
    IK (KS σ0) (checkCapAt (Z := Unit) nc src (checkCapAt (.threadCap t) sl (capInsert nc src dst))) := by
  unfold checkCapAt
  intro σ
  refine ikp_getCap_bind fun c' hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    intro hσ x hx
    have hk : KOk σ0 nc := (hσ _ _ hc').kd (kd_of_so hso)
    exact (ik_bind (SInvV.hv_getCap _) fun _ => ik_ite _ (ks_capInsert _ _ hk) (ik_pure _)) σ hσ x hx
  · exact ikp_of_ik (ik_pure _) σ

theorem ks_installTcbCap {σ0 : State Unit} (target : ObjRef) (slot : CslotPtr) (n : Nat)
    (o : Option (Cap × CslotPtr)) : IKE (KS σ0) (installTcbCap (Z := Unit) target slot n o) := by
  cases o with
  | none => unfold installTcbCap; exact ike_returnOk _
  | some p =>
    obtain ⟨c, sl⟩ := p
    unfold installTcbCap
    refine ike_bind (ks_capDelete _ σ0) fun _ => ?_
    exact ike_unlessE _ (ike_liftE (ks_checkCapAt_ins _ _ _ _ _))

theorem ks_installTcbFrameCap {σ0 : State Unit} (target : ObjRef) (slot : CslotPtr)
    (b : Option (VSpaceRef × Option (Cap × CslotPtr))) : IKE (KS σ0) (installTcbFrameCap (Z := Unit) target slot b) := by
  cases b with
  | none => unfold installTcbFrameCap; exact ike_returnOk _
  | some p =>
    obtain ⟨ptr, fr⟩ := p
    unfold installTcbFrameCap
    refine ike_bind (ks_capDelete _ σ0) fun _ => ?_
    refine ike_bind (ike_liftE (SInvV.hv_threadSet _ _ fun _ => rfl)) fun _ => ?_
    refine ike_bind (ike_liftE ?_) fun _ => ?_
    · cases fr with
      | none => exact ik_pure _
      | some q =>
        obtain ⟨c, sl⟩ := q
        exact ks_checkCapAt_ins _ _ _ _ _
    · exact ike_bind (ike_liftE (ik_gets _)) fun _ => ike_liftE (ik_when _ (SInvV.hv_rescheduleRequired))

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_installTcbCap _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_installTcbFrameCap _ _ _)

/-- **Every TCB invocation keeps `KS σ0`** (no decode fact). -/
theorem ks_invokeTcb {σ0 : State Unit} (i : TcbInvocation) : IKE (KS σ0) (invokeTcb (Z := Unit) i) := by
  cases i with
  | threadControlCaps t sl fh th cr vr buf =>
    unfold invokeTcb
    refine ike_bind (ks_installTcbCap _ _ 3 _) fun _ => ?_
    refine ike_bind (ks_installTcbCap _ _ 4 _) fun _ => ?_
    refine ike_bind (ks_installTcbCap _ _ 0 _) fun _ => ?_
    refine ike_bind (ks_installTcbCap _ _ 1 _) fun _ => ?_
    exact ike_bind (ks_installTcbFrameCap _ _ _) fun _ => ike_returnOk _
  | threadControlSched t sl fh mcp pr sc =>
    unfold invokeTcb
    refine ike_bind (ks_installTcbCap _ _ 3 _) fun _ => ?_
    hv_auto
  | _ => unfold invokeTcb; split <;> (try (rename_i heq; cases heq; done)) <;> hv_auto

/-! ## IPC cap transfer -/

/-- An arch cap whose range lies in another arch cap's. -/
theorem kd_arch_rng {a a' : ArchCap} (hr : ∀ r ∈ acRng a', r ∈ acRng a) :
    KD (.archObjectCap a) (.archObjectCap a') :=
  ⟨(fun _ _ e => by cases e), fun r h' => Or.inr ⟨hr r h', (fun _ e => by cases e)⟩⟩

/-- `derive_cap` of a page cap clears its mapping: same frame. -/
theorem kd_pageUnmap {dev r R mt pgs m} :
    KD (.archObjectCap (.pageCap dev r R mt pgs m)) (.archObjectCap (.pageCap dev r R .vmNoMap pgs none)) :=
  kd_arch_rng fun _ hr => hr

/-- **A derived cap is `KD` to its source.** -/
theorem kd_deriveCap (sl : CslotPtr) (c c' : Cap) (σ s : State Unit)
    (h : ((.ok c', s) : Except SyscallError Cap × State Unit) ∈ ((deriveCap (Z := Unit) sl c).run σ).1) :
    KD c c' := by
  revert c' s
  show OkDAt σ (fun _ c' => KD c c') (deriveCap (Z := Unit) sl c)
  cases c with
  | archObjectCap a =>
    simp only [deriveCap]; unfold archDeriveCap
    split <;> (first | exact okdAt_throw _ | exact okdAt_returnOk (kd_refl _) | exact okdAt_returnOk (kd_null _) | exact okdAt_returnOk (kd_pageUnmap))
  | untypedCap d b n f =>
    simp only [deriveCap]
    exact okdAt_bind fun _ _ _ => okdAt_returnOk (kd_refl _)
  | zombie => simp only [deriveCap]; exact okdAt_returnOk (kd_null _)
  | irqControlCap => simp only [deriveCap]; exact okdAt_returnOk (kd_null _)
  | _ => simp only [deriveCap]; exact okdAt_returnOk (kd_refl _)

/-- **`transfer_caps_loop`** of `KOk σ0` caps. -/
theorem ks_transferCapsLoop {σ0 : State Unit} (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      (∀ c ∈ cs, KOk σ0 c.1) → IK (KS σ0) (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi, _ => by unfold transferCapsLoop; exact ik_pure _
  | n, (c, s) :: cs, sl, mi, hcs => by
    have ih := fun sl' mi' => ks_transferCapsLoop (σ0 := σ0) ep rb (n + 1) cs sl' mi'
      (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
    unfold transferCapsLoop
    refine SInvV.hv_constOnFailure _ _ ?_
    refine ike_returnOk_bind ?_
    split
    · exact ike_bind (ike_liftE (SInvV.hv_setExtraBadge _ _ _)) fun _ => ike_liftE (ih _ _)
    · split
      · rename_i hne
        obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hne
        intro σ hσ
        refine ikpE_bind_ok (P := KS σ0) (SInvV.hv_deriveCap _ _ σ) (fun c' s' hd' => ?_) hσ
        have hk : KOk σ0 c' := (hcs (c, s) (by simp)).kd (kd_deriveCap _ _ _ _ _ hd')
        refine ikp_of_ik (?_ : IKE (KS σ0) _) s'
        refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
        refine ike_bind (ike_liftE (ks_capInsert _ _ hk)) fun _ => ?_
        exact ike_liftE (ih _ _)
      · exact ike_returnOk _

theorem ks_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (recv : ObjRef)
    (rbuf : Option ObjRef) {σ0 : State Unit} (hcs : ∀ c ∈ caps, KOk σ0 c.1) :
    IK (KS σ0) (transferCaps (Z := Unit) info caps ep recv rbuf) := by
  intro σ hσ x hx
  unfold transferCaps at hx
  obtain ⟨⟨slots, s1⟩, h1, hx⟩ := hx
  have hs1 : KS σ0 s1 := SInvV.hv_getReceiveSlots (P := KS σ0) recv rbuf σ hσ _ h1
  obtain ⟨⟨mi', s1'⟩, hz, hx⟩ := hx
  have hz' := Set.mem_singleton_iff.1 hz
  simp only [Prod.mk.injEq] at hz'
  obtain ⟨rfl, e'⟩ := hz'
  rw [e'] at hx
  dsimp only at hx
  cases rbuf with
  | none => rw [Set.mem_singleton_iff.1 hx]; exact hs1
  | some rb =>
    dsimp only at hx
    exact ks_transferCapsLoop ep rb 0 caps slots _ hcs s1 hs1 x hx

/-- The tail of `do_normal_transfer` after the extra-cap lookup. -/
theorem ks_dnt_tail (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (receiver : ObjRef)
    (rbuf : Option ObjRef) (mi : MessageInfo) (caps : List (Cap × CslotPtr)) {σ0 : State Unit}
    (hcs : ∀ c ∈ caps, KOk σ0 c.1) :
    IK (KS σ0) (do
      let mrsTransferred ← copyMrs (Z := Unit) sender sbuf receiver rbuf mi.miLength
      let mi' ← transferCaps mi caps ep receiver rbuf
      setMessageInfo receiver
          { miLength := mrsTransferred, miExtraCaps := mi'.miExtraCaps, miCapsUnwrapped := mi'.miCapsUnwrapped,
            miLabel := mi.miLabel }
      asUser receiver (setRegister badge_register badge)) :=
  ik_bind (SInvV.hv_copyMrs _ _ _ _ _) fun _ => ik_bind (ks_transferCaps _ _ _ _ _ hcs) fun _ =>
    ik_bind (SInvV.hv_setMessageInfo _ _) fun _ => SInvV.hv_asUser _ _

/-- **`do_normal_transfer` keeps `KS σ0`** (no outside fact). -/
theorem ks_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (receiver : ObjRef) (rbuf : Option ObjRef) : KK (doNormalTransfer (Z := Unit) sender sbuf ep badge grant receiver rbuf) := by
  intro σ0 σ hσ x hx
  unfold doNormalTransfer at hx
  obtain ⟨⟨mi, s1⟩, h1, hx⟩ := hx
  have hs1 : KS σ0 s1 := SInvV.hv_getMessageInfo (P := KS σ0) _ σ hσ _ h1
  dsimp only at hx
  cases grant
  · simp only [Bool.false_eq_true, ↓reduceIte] at hx
    obtain ⟨⟨caps, s2⟩, h2, hx⟩ := hx
    have h2' := Set.mem_singleton_iff.1 h2
    simp only [Prod.mk.injEq] at h2'
    obtain ⟨hc, hs⟩ := h2'
    rw [hc, hs] at hx
    exact ks_dnt_tail sender sbuf ep badge receiver rbuf mi [] (fun c h => by cases h) s1 hs1 x hx
  · simp only [↓reduceIte] at hx
    obtain ⟨⟨caps, s2⟩, h2, hx⟩ := hx
    unfold NonDetE.catch at h2
    obtain ⟨⟨r, s'⟩, hr, h2⟩ := h2
    have hs' : KS σ0 s' := SInvV.hv_lookupExtraCaps (P := KS σ0) _ _ _ s1 hs1 _ hr
    cases r with
    | ok a =>
      have h2' := Set.mem_singleton_iff.1 h2
      simp only [Prod.mk.injEq] at h2'
      obtain ⟨hc, hs⟩ := h2'
      rw [hc, hs] at hx
      have hin := okv_lookupExtraCaps (w := uV s1) _ _ _ s1 rfl a s' hr
      exact ks_dnt_tail sender sbuf ep badge receiver rbuf mi a (fun c hc => hs1.cap (hin c hc)) s' hs' x hx
    | error _ =>
      have h2' := Set.mem_singleton_iff.1 h2
      simp only [Prod.mk.injEq] at h2'
      obtain ⟨hc, hs⟩ := h2'
      rw [hc, hs] at hx
      exact ks_dnt_tail sender sbuf ep badge receiver rbuf mi [] (fun c h => by cases h) s' hs' x hx

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_doNormalTransfer _ _ _ _ _ _ _ _)

end

end Fl4Proofs.P3.SInvL
