/-
P3 (DESIGN.md §9), invariant line G1 (vih3): **the cap writers whose caps
come from slots** for `ValidIrqMasks ∧ ValidIrqHandlers` (spec side only;
outside the `JAtZ` cone).

* `OkV σ0 Pr m`: from any state with the caps and IRQ states of `σ0` (`hV`),
  every `.ok` outcome keeps them and its value satisfies `Pr`; combinators,
  `okv_mapME`, `okv_lookupCap` (a looked-up cap is `CA` by `ValidIrqHandlers`),
  `okv_lookupExtraCaps`, `okv_deriveCap` (`derive_cap` maps a handler cap only
  from the same handler cap).
* IPC: `vh_transferCapsLoop` (every transferred cap `CA`, carried in `R`),
  `vh_transferCaps`, `vi_doNormalTransfer` (the extra caps are looked up in the
  same transfer: `CA` by `ValidIrqHandlers` at the lookup, kept since the IRQ
  states do not change).
* `vi_irqIssue`: `set_irq_state IRQSignal irq` then `cap_insert (IRQHandlerCap
  irq)` (IRQ control, arch IRQ control, FL4's remapped IOAPIC issue).
* `vi_checkCapAt_ins`: the TCB installs' `check_cap_at newCap src (... cap_insert
  newCap ...)`: the source slot still holds a cap `same_object_as` the new cap,
  which for a handler cap is that cap (`CA` by `ValidIrqHandlers`).
* `vi_setCap_bind_dead`: a `set_cap cap` whose continuation fails for a handler
  cap (the page / page-table maps match the cap as an arch cap afterwards).
* `vh_invokeCnode` (`CnCA`: the inserted / moved / rotated caps `CA`),
  `vi_invokeIrqHandler` (`IhCA`: the ack's handler cap in a slot, the set-handler
  notification cap `CA`).
-/
import Fl4Proofs.P3.SpecInvValidIrqHandlersX
open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `OkV` -/

def OkV {ε α : Type} (σ0 : State Unit) (Pr : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ s, hV s = hV σ0 → OkDAt s (fun s' a => hV s' = hV σ0 ∧ Pr a) m

section OkVs
variable {ε α β : Type} {σ0 : State Unit}

theorem okv_bind {Q : α → Prop} {Pr : β → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : OkV σ0 Q m) (hg : ∀ a, Q a → OkV σ0 Pr (g a)) : OkV σ0 Pr (m >>= g) :=
  fun s hs => okdAt_bind fun a s' h => (hm s hs a s' h).elim fun e q => hg a q s' e

theorem okv_frame {m : NonDetE (State Unit) ε α} (hf : ∀ v, IKHE (fun s => hV s = v) m) :
    OkV σ0 (fun _ => True) m :=
  fun s hs a s' h => ⟨(hf (hV s) s rfl _ h).trans hs, trivial⟩

theorem okv_returnOk {Pr : α → Prop} {a : α} (h : Pr a) :
    OkV σ0 Pr (NonDetE.returnOk a : NonDetE (State Unit) ε α) := fun s hs => okdAt_returnOk ⟨hs, h⟩

theorem okv_pure {Pr : α → Prop} {a : α} (h : Pr a) : OkV σ0 Pr (pure a : NonDetE (State Unit) ε α) := by
  intro s hs b s' hb
  rw [ExceptT.run_pure] at hb
  have e := Set.mem_singleton_iff.1 hb
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨hs, h⟩

theorem okv_throw {Pr : α → Prop} (e : ε) : OkV σ0 Pr (NonDetE.throwError e : NonDetE (State Unit) ε α) :=
  fun s _ => okdAt_throw e

theorem okv_ite {Pr : α → Prop} (c : Prop) [Decidable c] {m1 m2 : NonDetE (State Unit) ε α}
    (h1 : OkV σ0 Pr m1) (h2 : OkV σ0 Pr m2) : OkV σ0 Pr (if c then m1 else m2) := by
  split <;> assumption

theorem okv_mono {Pr Q : α → Prop} {m : NonDetE (State Unit) ε α} (h : OkV σ0 Q m) (hq : ∀ a, Q a → Pr a) :
    OkV σ0 Pr m := fun s hs a s' h' => (h s hs a s' h').imp_right (hq a)

theorem okv_mapME {Pr : β → Prop} {F : α → NonDetE (State Unit) ε β} (h : ∀ a, OkV σ0 Pr (F a)) :
    ∀ xs : List α, OkV σ0 (fun bs => ∀ b ∈ bs, Pr b) (NonDetE.mapME F xs)
  | [] => by unfold NonDetE.mapME; exact okv_pure (fun _ h => by cases h)
  | a :: t => by
    unfold NonDetE.mapME
    exact okv_bind (h a) fun b hb => okv_bind (okv_mapME h t) fun bs hbs =>
      okv_pure fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hb
        · exact hbs x hx

end OkVs

theorem vih_of_hV {σ σ' : State Unit} (e : hV σ' = hV σ) (h : ValidIrqHandlers σ) : ValidIrqHandlers σ' :=
  fun p cref irq hc => by rw [hV_is e]; exact h p cref irq (by rw [← hV_cap e]; exact hc)

/-- A looked-up cap is `CA`. -/
theorem okv_lookupCap {σ0 : State Unit} (hv : ValidIrqHandlers σ0) (t : ObjRef) (c : CapRef) (cp : ObjRef) (rp : Bool) :
    OkV σ0 (fun r : Cap × CslotPtr => CA r.1 σ0.interruptStates)
      (capFaultOnFailure (Z := Unit) cp rp (lookupCapAndSlot t c)) := by
  intro s hs a s' h
  have e : hV s' = hV s :=
    hv_capFaultOnFailure (P := fun x => hV x = hV s) cp rp _ (hv_lookupCapAndSlot t c) s rfl _ h
  have hc := okdAt_capFault cp rp (okCap_lookupCapAndSlot t c s) a s' h
  have e' := e.trans hs
  refine ⟨e', ?_⟩
  have := ca_of_slot (vih_of_hV e' hv) hc
  rw [hV_is e'] at this; exact this

theorem okv_lookupExtraCaps {σ0 : State Unit} (hv : ValidIrqHandlers σ0) (t : ObjRef) (b : Option Data)
    (mi : MessageInfo) :
    OkV σ0 (fun caps : List (Cap × CslotPtr) => ∀ c ∈ caps, CA c.1 σ0.interruptStates)
      (lookupExtraCaps (Z := Unit) t b mi) := by
  unfold lookupExtraCaps
  exact okv_bind (okv_frame fun v => ike_liftE (P := fun s => hV s = v) (hv_getExtraCptrs _ _)) fun cptrs _ =>
    okv_mapME (fun _ => okv_lookupCap hv _ _ _ _) cptrs

theorem okv_deriveCap {σ0 : State Unit} (sl : CslotPtr) (c : Cap) (hc : CA c σ0.interruptStates) :
    OkV σ0 (fun c' => CA c' σ0.interruptStates) (deriveCap (Z := Unit) sl c) := by
  cases c with
  | archObjectCap a =>
    simp only [deriveCap]; unfold archDeriveCap
    split <;> first | exact okv_throw _ | exact okv_returnOk (ca_noH (fun _ h => by cases h) _)
  | untypedCap d b n f =>
    simp only [deriveCap]
    exact okv_bind (okv_frame fun v => hv_ensureNoChildren (P := fun s => hV s = v) _) fun _ _ => okv_returnOk hc
  | zombie => simp only [deriveCap]; exact okv_returnOk (ca_noH (fun _ h => by cases h) _)
  | irqControlCap => simp only [deriveCap]; exact okv_returnOk (ca_noH (fun _ h => by cases h) _)
  | _ => simp only [deriveCap]; exact okv_returnOk hc

/-! ## IPC cap transfer -/

theorem vh_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo)
      (R : (Irq → IrqState) → Prop), (∀ is, R is → ∀ c ∈ caps, CA c.1 is) →
      IKH (VH R) (transferCapsLoop (Z := Unit) ep rb n caps sl mi)
  | n, [], sl, mi, R, _ => by unfold transferCapsLoop; exact ik_pure _
  | n, (c, s) :: cs, sl, mi, R, hR => by
    have ih := fun sl' mi' R' hR' => vh_transferCapsLoop ep rb (n + 1) cs sl' mi' R' hR'
    have hR1 : ∀ is, R is → ∀ c' ∈ cs, CA c'.1 is := fun is h c' hc' => hR is h c' (List.mem_cons_of_mem _ hc')
    unfold transferCapsLoop constOnFailure
    refine ik_catch ?_ (fun _ => ik_pure' _)
    refine ike_returnOk_bind ?_
    split
    · exact ike_bind (ike_liftE (hv_setExtraBadge _ _ _)) fun _ => ike_liftE (ih _ _ R hR1)
    · split
      · intro σ h x hx
        obtain ⟨z, hz, ⟨c', hc', hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
        · obtain ⟨r, s1⟩ := z
          simp only at hc'; subst hc'
          have hs1 : VH R s1 := hv_deriveCap (P := VH R) _ _ σ h _ hz
          have hca := (okv_deriveCap (σ0 := σ) s c (hR _ h.2.2 (c, s) (List.mem_cons_self ..)) σ rfl c' s1 hz)
          have hca' : CA c' s1.interruptStates := by rw [hV_is hca.1]; exact hca.2
          have := (show IKHE (VH fun is => R is ∧ CA c' is) _ from by
            refine ike_bind (ike_whenE _ (ike_throw _)) fun _ =>
              ike_bind (ike_liftE (vh_capInsert _ _ _ fun _ h => h.2)) fun _ =>
              ike_liftE (ih _ _ _ fun is h => hR1 is h.1)) s1 ⟨hs1.1, hs1.2.1, hs1.2.2, hca'⟩ x hx
          exact ⟨this.1, this.2.1, this.2.2.1⟩
        · exact hv_deriveCap (P := VH R) _ _ σ h _ hz
      · exact ike_returnOk _

theorem vh_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (r : ObjRef)
    (rb : Option ObjRef) {R : (Irq → IrqState) → Prop} (hR : ∀ is, R is → ∀ c ∈ caps, CA c.1 is) :
    IKH (VH R) (transferCaps (Z := Unit) info caps ep r rb) := by
  unfold transferCaps
  refine ik_bind (hv_getReceiveSlots _ _) fun _ => ik_pure_bind ?_
  split
  · exact ik_pure _
  · exact vh_transferCapsLoop _ _ _ _ _ _ R hR

/-- A bind whose first step yields a carried IRQ-state fact for the rest. -/
theorem ik_bind_vh_carry {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    {Q : α → (Irq → IrqState) → Prop} (hm : ∀ σ, VI σ → ∀ y ∈ (m σ).1, VI y.2 ∧ Q y.1 y.2.interruptStates)
    (hk : ∀ a, IKH (VH (Q a)) (k a)) : IKH VI (m >>= k) := by
  intro σ h x ⟨y, hy, hx⟩
  obtain ⟨h1, hq⟩ := hm σ h y hy
  have := hk y.1 y.2 ⟨h1.1, h1.2.1, hq⟩ x hx
  exact ⟨this.1, this.2.1, trivial⟩

theorem vi_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (receiver : ObjRef) (rbuf : Option ObjRef) :
    IKH VI (doNormalTransfer (Z := Unit) sender sbuf ep badge grant receiver rbuf) := by
  unfold doNormalTransfer
  refine ik_bind (hv_getMessageInfo _) fun mi => ?_
  dsimp only
  split
  all_goals refine ik_bind_vh_carry (Q := fun (caps : List (Cap × CslotPtr)) is => ∀ c ∈ caps, CA c.1 is) ?_ (fun caps => ?_)
  · intro σ h y hy
    unfold NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨r, s⟩ := z
    have hs : VI s := hv_lookupExtraCaps (P := VI) _ _ _ σ h _ hz
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      obtain ⟨e, hca⟩ := okv_lookupExtraCaps h.2.1 _ _ _ σ rfl a s hz
      exact ⟨hs, fun c hc => by rw [hV_is e]; exact hca c hc⟩
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, fun c hc => by cases hc⟩
  · refine ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (vh_transferCaps _ _ _ _ _ fun _ h => h) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _
  · intro σ h y hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨h, fun c hc => by cases hc⟩
  · refine ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (vh_transferCaps _ _ _ _ _ fun _ h => h) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_doNormalTransfer _ _ _ _ _ _ _)

/-! ## IRQ control issue, TCB installs, page maps -/

theorem vi_irqIssue (irq : Irq) (src dst : CslotPtr) :
    IKH VI (setIrqState (Z := Unit) .irqSignal irq >>= fun _ => capInsert (Z := Unit) (.irqHandlerCap irq) src dst) := by
  intro σ h x ⟨y, hy, hx⟩
  obtain ⟨-, hi⟩ := setIrqState_out hy
  have h1 : VI y.2 := vh_setIrqState_active rm_true (fun e => by cases e) irq σ h y hy
  have h2 := vh_capInsert (R := fun is => is irq ≠ .irqInactive) (.irqHandlerCap irq) src dst
    (fun is h irq' e => by cases e; exact h) y.2 ⟨h1.1, h1.2.1, by simp [hi]⟩ x hx
  exact ⟨h2.1, h2.2.1, trivial⟩

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_irqIssue _ _ _)

theorem sameObjectAs_handler {irq : Irq} {c : Cap} (h : sameObjectAs (.irqHandlerCap irq) c) :
    c = .irqHandlerCap irq := by
  cases c <;> simp_all [sameObjectAs, sameRegionAs]

theorem vi_checkCapAt_ins (nc : Cap) (src : CslotPtr) (t : ObjRef) (sl dst : CslotPtr) :
    IKH VI (checkCapAt (Z := Unit) nc src (checkCapAt (.threadCap t) sl (capInsert nc src dst))) := by
  unfold checkCapAt
  refine ik_getCap_bind fun c' σ hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    intro h
    have hca : CA nc σ.interruptStates := fun irq e => by
      subst e
      exact ca_of_slot h.2.1 ((sameObjectAs_handler hso) ▸ hc') irq rfl
    exact ikp_vh_and (Q := CA nc) (ik_bind (hv_getCap _) fun _ =>
      ik_ite _ (vh_capInsert _ _ _ fun _ h => h.2) (ik_pure _)) hca h
  · exact ikp_of_ik (ik_pure _) σ

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_checkCapAt_ins _ _ _ _ _)

theorem vi_setCap_bind_dead {β : Type} (cap : Cap) (sl : CslotPtr) {k : Unit → NonDet (State Unit) β}
    (hk : ∀ a, IKH VI (k a)) (hd : ∀ irq, cap = .irqHandlerCap irq → ∀ a σ x, x ∈ (k a σ).1 → False) :
    IKH VI (setCap (Z := Unit) cap sl >>= k) := by
  intro σ h x ⟨y, hy, hx⟩
  by_cases hc : ∃ irq, cap = .irqHandlerCap irq
  · obtain ⟨irq, e⟩ := hc; exact (hd irq e _ _ x hx).elim
  · exact hk _ _ (vh_setCap cap sl (fun _ _ => ca_noH (fun irq e => hc ⟨irq, e⟩) _) σ h y hy) x hx

/-- The dead continuation: the second bind's head fails. -/
macro "dead_k" : tactic => `(tactic| (intro irq e _ _ x hx; subst e; obtain ⟨_, _, _, hf, _⟩ := hx; first | exact hf | (simp [NonDet.fail] at hf) | cases hf))

/-- The same with the map entry matched first (the page map). -/
macro "dead_k2" : tactic => `(tactic| (intro irq e _ _ x hx; subst e; revert hx; split <;> (intro hx; obtain ⟨_, _, hx⟩ := hx; obtain ⟨_, hf, _⟩ := hx; first | exact hf | cases hf)))

theorem vi_performPageInvocation (iv : PageInvocation) : IKH VI (performPageInvocation (Z := Unit) iv) := by
  cases iv with
  | pageMap cap sl ent vs =>
    simp only [performPageInvocation]
    refine vi_setCap_bind_dead _ _ (fun _ => by hv_auto) ?_
    dead_k2
  | _ => simp only [performPageInvocation]; hv_auto

theorem vi_performPageTableInvocation (iv : PageTableInvocation) :
    IKH VI (performPageTableInvocation (Z := Unit) iv) := by
  cases iv with
  | pageTableMap cap sl pde pd vs =>
    simp only [performPageTableInvocation]
    exact vi_setCap_bind_dead _ _ (fun _ => by hv_auto) (by dead_k)
  | _ => simp only [performPageTableInvocation]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

theorem vi_performPageDirectoryInvocation (iv : PageDirectoryInvocation) :
    IKH VI (performPageDirectoryInvocation (Z := Unit) iv) := by
  cases iv with
  | pageDirectoryMap cap sl pde pd vs =>
    simp only [performPageDirectoryInvocation]
    exact vi_setCap_bind_dead _ _ (fun _ => by hv_auto) (by dead_k)
  | _ => simp only [performPageDirectoryInvocation]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

theorem vi_performPdptInvocation (iv : PdptInvocation) : IKH VI (performPdptInvocation (Z := Unit) iv) := by
  cases iv with
  | pdptMap cap sl pde pd vs =>
    simp only [performPdptInvocation]
    exact vi_setCap_bind_dead _ _ (fun _ => by hv_auto) (by dead_k)
  | _ => simp only [performPdptInvocation]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_performPageInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_performPageTableInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_performPageDirectoryInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_performPdptInvocation _)

theorem ca_freeIndexUpdate {c : Cap} {is : Irq → IrqState} (h : CA c is) (g : Nat → Nat) :
    CA (freeIndexUpdate g c) is := by
  intro irq e; apply h irq; cases c <;> simp_all [freeIndexUpdate]

/-- The ASID pool creation: the parent untyped cap re-written full (read from its slot). -/
theorem vi_performAsidControlInvocation (iv : AsidControlInvocation) :
    IKH VI (performAsidControlInvocation (Z := Unit) iv) := by
  cases iv with
  | makePool frame slot parent base =>
    simp only [performAsidControlInvocation]
    refine ik_bind (vh_deleteObjects _ _) fun _ => ik_getCap_bind fun pcap σ hp => ?_
    intro h
    refine ikp_bind (vh_setCap_p _ _ σ fun h' => ca_freeIndexUpdate (ca_of_slot h'.2.1 hp) _) (fun _ => ?_) h
    hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_performAsidControlInvocation _)

/-! ## CNode and IRQ handler performs -/

/-- The caps a CNode invocation writes are `CA`. -/
def CnCA (i : CnodeInvocation) (is : Irq → IrqState) : Prop :=
  match i with
  | .insertCall c _ _ => CA c is
  | .moveCall c _ _ => CA c is
  | .rotateCall c1 c2 _ _ _ => CA c1 is ∧ CA c2 is
  | _ => True

theorem vh_invokeCnode (i : CnodeInvocation) : IKHE (ε := Unit) (VH (CnCA i)) (invokeCnode (Z := Unit) i) := by
  cases i with
  | insertCall c s d => exact ike_liftE (vh_capInsert c s d fun _ h => h)
  | moveCall c s d => exact ike_liftE (vh_capMove c s d fun _ h => h)
  | rotateCall c1 c2 s1 s2 s3 =>
    refine ike_liftE ?_
    split
    · exact vh_capSwap _ _ _ _ (fun _ h => h.1) (fun _ h => h.2)
    · exact ik_bind (vh_capMove _ _ _ fun _ h => h.2) fun _ => vh_capMove _ _ _ fun _ h => h.1
  | revokeCall s => exact vi_capRevoke s
  | deleteCall s => exact vi_capDelete s
  | cancelBadgedSendsCall c => simp only [invokeCnode]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

/-- The facts an IRQ handler invocation needs at its perform. -/
def IhCA (i : IrqHandlerInvocation) (σ : State Unit) : Prop :=
  match i with
  | .aCKIrq irq => HIrq σ irq
  | .setIRQHandler _ c _ => CA c σ.interruptStates
  | .clearIRQHandler _ => True

theorem vi_invokeIrqHandler (i : IrqHandlerInvocation) (σ : State Unit) (h : VI σ) (hc : IhCA i σ) :
    ∀ x ∈ (invokeIrqHandler (Z := Unit) i σ).1, VI x.2 := by
  cases i with
  | aCKIrq irq =>
    intro x hx
    exact ⟨(vimh_invokeIrqHandler_ack h.1 h.2.1 hc x hx).1, (vimh_invokeIrqHandler_ack h.1 h.2.1 hc x hx).2, trivial⟩
  | setIRQHandler irq c sl =>
    have hU : WLH (fun s : State Unit => CA c s.interruptStates) :=
      wlh_of_hV fun _ _ e h => by rw [hV_is e]; exact h
    have hd : ∀ s', IKH (VH (CA c)) (capDeleteOne (Z := Unit) s') := by
      intro s' σ h x hx
      have r := vi_capDeleteOne_u (U := fun s => CA c s.interruptStates)
        (fun sl σ x h hx => by obtain ⟨o, r⟩ := sl; rw [(vih_setCap_out hx).1]; exact h) s' σ
        ⟨⟨h.1, h.2.1, trivial⟩, h.2.2⟩ x hx
      exact ⟨r.1.1, r.1.2.1, r.2⟩
    have key : IKH (VH (CA c)) (invokeIrqHandler (Z := Unit) (.setIRQHandler irq c sl)) := by
      simp only [invokeIrqHandler]
      exact ik_bind (hv_getIrqSlot _) fun s => ik_bind (hd s) fun _ => vh_capInsert c sl s fun _ h => h
    intro x hx
    have := key σ ⟨h.1, h.2.1, hc⟩ x hx
    exact ⟨this.1, this.2.1, trivial⟩
  | clearIRQHandler irq =>
    simp only [invokeIrqHandler]
    exact ik_bind (hv_getIrqSlot _) (fun s => vi_capDeleteOne s) σ h

end

end Fl4Proofs.P3.SInvV
