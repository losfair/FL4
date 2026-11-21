/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **spec-only
invariants kept by a whole kernel entry: the kit** (spec side only; outside
the `JAtZ` cone).

* `IK P m`: every outcome of `m` from a `P` state is a `P` state (l4v
  `⦃P⦄ m ⦃λ_. P⦄`), `IKE` for the exception monad; combinators mirroring
  VsDom's `FK` ones.
* `vw σ`: the current time, the last machine time, the interrupt table and
  the IRQ masks (what `ValidMachineTime` and `ValidIrqMasks` read).
* `WL P`: the leaves a predicate `P` reading only `vw` must be kept by:
  `updateTimeStamp`, `setIrqState`, machine operations that keep the last
  machine time and only set IRQ masks (`MaskT`, among them the spec's
  ReadFPU step `fl4FpuToFrame`, which changes only the user memory since
  fpu1; before, it set the whole machine state: invB's FINDING), and the
  IRQ ack's unmask.
  `GK m := ∀ P, WL P → IK P m`: proved once for every spec function of the
  kernel entry (SpecInvValidMachineTimeGen), instantiated per field.
* Frames: MachFieldFamT's `MTK` family (every spec function not reaching a
  machine-time / IRQ writer) gives `GK` (`gk_of_mtk`), since `msFT` contains
  `vw`.
-/
import Fl4Proofs.P3.MachFieldFamT
import Fl4Spec.Ext.Entry

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT

noncomputable section

/-! ## Invariant-kept triples -/

/-- Every outcome of `m` from a `P` state is a `P` state. -/
def IK (P : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x ∈ (m σ).1, P x.2

/-- `IK` for the exception monad. -/
def IKE (P : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  IK P (ExceptT.run m)

/-! ## The view and the leaves -/

/-- The fields `ValidMachineTime` and `ValidIrqMasks` read. -/
def vw (σ : State Unit) :=
  (σ.curTime, σ.machineState.lastMachineTime, σ.interruptStates, σ.machineState.irqMasks)

/-- A machine operation keeping the last machine time and only masking
(setting IRQ masks to `true`). -/
def MaskT {α : Type} (m : NonDet MachineState α) : Prop :=
  ∀ ms x, x ∈ (m ms).1 → x.2.lastMachineTime = ms.lastMachineTime ∧
    ∀ j, x.2.irqMasks j = ms.irqMasks j ∨ x.2.irqMasks j = true

/-- The leaves of a predicate reading `vw`. -/
structure WL (P : State Unit → Prop) : Prop where
  view : ∀ σ σ', vw σ' = vw σ → P σ → P σ'
  uts : IK P (updateTimeStamp (Z := Unit))
  sis : ∀ st i, IK P (setIrqState (Z := Unit) st i)
  msk : ∀ {α : Type} (mop : NonDet MachineState α), MaskT mop → IK P (doMachineOp (Z := Unit) mop)
  ack : ∀ i, IK P (doMachineOp (Z := Unit) (maskInterrupt false i))

/-- Kept by every predicate with the leaves. -/
def GK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ P, WL P → IK P m

/-- `GK` for the exception monad. -/
def GKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := GK (ExceptT.run m)

theorem GK.ik {P : State Unit → Prop} (L : WL P) {α : Type} {m : NonDet (State Unit) α} (h : GK m) : IK P m :=
  h P L

/-! ## Frames -/

theorem gk_of_fk {α : Type} {m : NonDet (State Unit) α} (h : FK vw m) : GK m :=
  fun _ L σ hP x hx => L.view σ x.2 (h σ x hx) hP

theorem vw_of_msFT {σ σ' : State Unit} (h : msFT σ' = msFT σ) : vw σ' = vw σ := by
  unfold msFT msF at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨⟨h1, -, -, h4, h5⟩, h6⟩ := h
  unfold vw; rw [h1, h4, h5, h6]

theorem gk_of_mtk {α : Type} {m : NonDet (State Unit) α} (h : MTK m) : GK m :=
  gk_of_fk fun σ x hx => vw_of_msFT (h σ x hx)

theorem gke_of_mtke {ε α : Type} {m : NonDetE (State Unit) ε α} (h : MTKE m) : GKE m :=
  gk_of_mtk h

/-! ## Combinators -/

section Comb

theorem gk_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : GK m)
    (hg : ∀ a, GK (g a)) : GK (m >>= g) := by
  intro P L σ h x ⟨y, hy, hx⟩
  exact hg y.1 P L y.2 (hm P L σ h y hy) x hx

theorem gk_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : GK m)
    (hg : ∀ a, GK (g a)) : GK (NonDet.bind m g) := gk_bind hm hg

theorem gk_pure {α : Type} (a : α) : GK (pure a : NonDet (State Unit) α) := gk_of_fk (dk_pure a)

theorem gk_pure' {α : Type} (a : α) : GK (NonDet.pure a : NonDet (State Unit) α) := gk_of_fk (dk_pure a)

theorem gk_gets {α : Type} (g : State Unit → α) : GK (NonDet.gets g) := gk_of_fk (dk_gets g)

theorem gk_get : GK (NonDet.get : NonDet (State Unit) (State Unit)) := gk_of_fk dk_get

theorem gk_assert (P : Prop) : GK (NonDet.assert P : NonDet (State Unit) Unit) := gk_of_fk (dk_assert P)

theorem gk_fail {α : Type} : GK (NonDet.fail : NonDet (State Unit) α) := gk_of_fk dk_fail

theorem gk_assertOpt {α : Type} (o : Option α) : GK (NonDet.assertOpt o : NonDet (State Unit) α) :=
  gk_of_fk (dk_assertOpt o)

theorem gk_getsThe {α : Type} (g : State Unit → Option α) : GK (NonDet.getsThe g) := gk_of_fk (dk_getsThe g)

theorem gk_selectF {α : Type} (S : Set α × Prop) : GK (NonDet.selectF S : NonDet (State Unit) α) :=
  gk_of_fk (dk_selectF S)

theorem gk_select {α : Type} (S : Set α) : GK (NonDet.select S : NonDet (State Unit) α) := gk_of_fk (dk_select S)

theorem gk_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : GK m1)
    (h2 : GK m2) : GK (if Q then m1 else m2) := by
  split <;> assumption

theorem gk_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : GK m) : GK (NonDet.when Q m) := by
  unfold NonDet.when; exact gk_ite Q h (gk_pure' _)

theorem gk_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : GK m) :
    GK (NonDet.unless Q m) := by
  unfold NonDet.unless; exact gk_ite Q (gk_pure' _) h

theorem gk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, GK (g a)) (o : Option α) :
    GK (NonDet.maybeM g o) := by
  cases o
  · exact gk_pure' _
  · exact h _

theorem gk_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : GK m) : GK (NonDet.liftM g m) :=
  gk_bind' h fun _ => gk_pure' _

theorem gk_modify {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) : GK (NonDet.modify g) :=
  gk_of_fk (dk_modify hg)

theorem gk_get_put {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) :
    GK (NonDet.get >>= fun s => NonDet.put (g s)) := gk_of_fk (dk_get_put hg)

theorem gk_get_put' {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) :
    GK (do let s ← NonDet.get; NonDet.put (g s)) := gk_get_put hg

theorem gk_getObject (p : ObjRef) : GK (getObject (Z := Unit) p) := gk_getsThe _

theorem gk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, GK (B r)) (r : α) : GK (NonDet.whileLoop C B r) := by
  intro P L σ h x hx
  induction hx with
  | done _ => exact h
  | step _ hm _ ih => exact ih (hB _ P L _ h _ hm)

theorem gk_mapMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GK (g a)) (xs : List α) :
    GK (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact gk_pure' _
  | cons a xs' ih => exact gk_bind' (h a) fun _ => ih

theorem gk_forMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GK (g a)) (xs : List α) :
    GK (NonDet.forMx xs g) := gk_mapMx h xs

theorem gk_mapM {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GK (g a)) (xs : List α) :
    GK (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact gk_pure' _
  | cons a xs' ih => exact gk_bind' (h a) fun _ => gk_bind' ih fun _ => gk_pure' _

end Comb

section CombE
variable {ε : Type}

theorem gke_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : GKE m)
    (hg : ∀ a, GKE (g a)) : GKE (m >>= g) := by
  unfold GKE; rw [ExceptT.run_bind]
  refine gk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact gk_pure _

theorem gke_pure {α : Type} (a : α) : GKE (pure a : NonDetE (State Unit) ε α) := gk_pure _

theorem gke_returnOk {α : Type} (a : α) : GKE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := gk_pure _

theorem gke_throw {α : Type} (e : ε) : GKE (NonDetE.throwError e : NonDetE (State Unit) ε α) := gk_pure _

theorem gke_throw' {α : Type} (e : ε) : GKE (throw e : NonDetE (State Unit) ε α) := gk_pure _

theorem gke_liftE {α : Type} {m : NonDet (State Unit) α} (h : GK m) : GKE (NonDetE.liftE (ε := ε) m) := by
  unfold GKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact gk_bind h fun _ => gk_pure _

theorem gke_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDetE (State Unit) ε α} (h1 : GKE m1)
    (h2 : GKE m2) : GKE (if Q then m1 else m2) := by
  split <;> assumption

theorem gke_whenE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : GKE m) :
    GKE (NonDetE.whenE Q m) := by
  unfold NonDetE.whenE; exact gke_ite Q h (gke_pure _)

theorem gke_unlessE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : GKE m) :
    GKE (NonDetE.unlessE Q m) := by
  unfold NonDetE.unlessE; exact gke_ite Q (gke_pure _) h

theorem gke_throwOpt {α : Type} (e : ε) (o : Option α) : GKE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact gke_throw' e
  · exact gke_pure _

theorem gke_assertE (Q : Prop) : GKE (NonDetE.assertE Q : NonDetE (State Unit) ε Unit) :=
  gke_liftE (gk_assert Q)

theorem gk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : GKE m)
    (hh : ∀ e, GK (h e)) : GK (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine gk_bind' hm fun r => ?_
  cases r with
  | ok a => exact gk_pure' _
  | error e => exact hh e

theorem gke_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : GKE m) (hh : ∀ e, GKE (h e)) : GKE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE GKE
  rw [ExceptT.run_mk]
  refine gk_bind' hm fun r => ?_
  cases r with
  | ok a => exact gk_pure' _
  | error e => exact hh e

theorem gke_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : GKE m) :
    GKE (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact gke_bind h fun _ => gke_pure _

theorem gke_mapMEx {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, GKE (F a)) :
    ∀ xs : List α, GKE (NonDetE.mapMEx F xs)
  | [] => by unfold NonDetE.mapMEx; exact gke_pure _
  | a :: xs => by unfold NonDetE.mapMEx; exact gke_bind (h a) fun _ => gke_mapMEx h xs

theorem gke_mapME {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, GKE (F a)) :
    ∀ xs : List α, GKE (NonDetE.mapME F xs)
  | [] => by unfold NonDetE.mapME; exact gke_pure _
  | a :: xs => by
    unfold NonDetE.mapME; exact gke_bind (h a) fun _ => gke_bind (gke_mapME h xs) fun _ => gke_pure _

theorem gke_withoutPreemption {α : Type} {m : SMonad Unit α} (h : GK m) :
    GKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact gke_liftE h

theorem gke_capFaultOnFailure {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : GKE m) :
    GKE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact gke_handleE h fun _ => gke_throw _

theorem gke_lookupErrorOnFailure {α : Type} (b : Bool) {m : LFMonad Unit α} (h : GKE m) :
    GKE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact gke_handleE h fun _ => gke_throw _

theorem gke_unifyFailure {F α : Type} {m : NonDetE (State Unit) F α} (h : GKE m) :
    GKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact gke_handleE h fun _ => gke_throw _

theorem gk_emptyOnFailure {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : GKE m) :
    GK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact gk_catch h fun _ => gk_pure' _

theorem gk_constOnFailure {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : GKE m) :
    GK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact gk_catch h fun _ => gk_pure' _

end CombE

/-! ## Machine operations that only mask -/

section MaskT

theorem mt_bind {α β : Type} {m : NonDet MachineState α} {g : α → NonDet MachineState β} (hm : MaskT m)
    (hg : ∀ a, MaskT (g a)) : MaskT (m >>= g) := by
  intro ms x ⟨y, hy, hx⟩
  obtain ⟨a1, b1⟩ := hm ms y hy
  obtain ⟨a2, b2⟩ := hg y.1 y.2 x hx
  refine ⟨a2.trans a1, fun j => ?_⟩
  rcases b2 j with e | e
  · rw [e]; exact b1 j
  · exact Or.inr e

theorem mt_bind' {α β : Type} {m : NonDet MachineState α} {g : α → NonDet MachineState β} (hm : MaskT m)
    (hg : ∀ a, MaskT (g a)) : MaskT (NonDet.bind m g) := mt_bind hm hg

theorem mt_pure {α : Type} (a : α) : MaskT (pure a : NonDet MachineState α) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, fun _ => Or.inl rfl⟩

theorem mt_pure' {α : Type} (a : α) : MaskT (NonDet.pure a : NonDet MachineState α) := mt_pure a

theorem mt_gets {α : Type} (g : MachineState → α) : MaskT (NonDet.gets g) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, fun _ => Or.inl rfl⟩

theorem mt_modify {g : MachineState → MachineState}
    (hg : ∀ ms, (g ms).lastMachineTime = ms.lastMachineTime ∧
      ∀ j, (g ms).irqMasks j = ms.irqMasks j ∨ (g ms).irqMasks j = true) : MaskT (NonDet.modify g) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg ms

theorem mt_select {α : Type} (A : Set α) : MaskT (NonDet.select A : NonDet MachineState α) := by
  intro ms x hx; rw [hx.2]; exact ⟨rfl, fun _ => Or.inl rfl⟩

/-- The spec's ReadFPU machine step (Ext/Tcb `fl4FpuToFrame`, fpu1): only the
user memory changes. -/
theorem mt_fl4FpuToFrame (f : Word) : MaskT (fl4FpuToFrame f) := by
  unfold fl4FpuToFrame
  exact mt_bind (mt_gets _) fun _ => mt_bind (mt_select _) fun _ =>
    mt_modify fun _ => ⟨rfl, fun _ => Or.inl rfl⟩

theorem mt_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet MachineState α} (h1 : MaskT m1)
    (h2 : MaskT m2) : MaskT (if Q then m1 else m2) := by
  split <;> assumption

theorem mt_mapMx {α γ : Type} {g : α → NonDet MachineState γ} (h : ∀ a, MaskT (g a)) (xs : List α) :
    MaskT (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact mt_pure' _
  | cons a xs' ih => exact mt_bind' (h a) fun _ => ih

theorem mt_of_mkf {α : Type} {m : NonDet MachineState α} (h : MKF m) : MaskT m := by
  intro ms x hx
  have e := h ms x hx
  unfold mF at e
  simp only [Prod.mk.injEq] at e
  exact ⟨e.2.2.2, fun j => Or.inl (congrFun e.1 j)⟩

theorem mt_maskInterrupt_true (i : Irq) : MaskT (maskInterrupt true i) := by
  unfold maskInterrupt
  refine mt_modify fun ms => ⟨rfl, fun j => ?_⟩
  by_cases h : j = i
  · subst h; exact Or.inr (by simp)
  · exact Or.inl (by simp [h])

theorem mt_getActiveIRQ (b : Bool) : MaskT (getActiveIRQ b) := by
  unfold getActiveIRQ
  refine mt_bind (mt_gets _) fun _ => mt_bind (mt_modify fun _ => ⟨rfl, fun _ => Or.inl rfl⟩) fun _ =>
    mt_bind (mt_gets _) fun _ => mt_ite _ (mt_pure _) (mt_pure _)

theorem mt_ackInterrupt (i : Irq) : MaskT (ackInterrupt i) := mt_pure _

theorem mt_machineOpLift (f : MachineRestMonad Unit) : MaskT (machineOpLift f) := mt_of_mkf (mkf_machineOpLift f)

theorem mt_storeWord (p w : Word) : MaskT (storeWord p w) := mt_of_mkf (mkf_storeWord p w)

theorem mt_clearMemory (p : Word) (n : Nat) : MaskT (clearMemory p n) := by
  unfold clearMemory; exact mt_mapMx (fun _ => mt_storeWord _ _) _

theorem mt_freeMemory (p : Word) (n : Nat) : MaskT (freeMemory p n) := by
  unfold freeMemory; exact mt_mapMx (fun _ => mt_storeWord _ _) _

theorem mt_setDeadline (d : Word64) : MaskT (setDeadline d) := by unfold setDeadline; exact mt_machineOpLift _
theorem mt_ackDeadlineIRQ : MaskT ackDeadlineIRQ := by unfold ackDeadlineIRQ; exact mt_ackInterrupt _
theorem mt_in8 (p : Word16) : MaskT (in8 p) := by unfold in8; exact mt_bind (mt_machineOpLift _) fun _ => mt_gets _
theorem mt_in16 (p : Word16) : MaskT (in16 p) := by unfold in16; exact mt_bind (mt_machineOpLift _) fun _ => mt_gets _
theorem mt_in32 (p : Word16) : MaskT (in32 p) := by unfold in32; exact mt_bind (mt_machineOpLift _) fun _ => mt_gets _
theorem mt_out8 (p : Word16) (d : Word8) : MaskT (out8 p d) := by unfold out8; exact mt_machineOpLift _
theorem mt_out16 (p : Word16) (d : Word16) : MaskT (out16 p d) := by unfold out16; exact mt_machineOpLift _
theorem mt_out32 (p : Word16) (d : Word32) : MaskT (out32 p d) := by unfold out32; exact mt_machineOpLift _
theorem mt_ioapicMapPinToVector (a b c d e : Word) : MaskT (ioapicMapPinToVector a b c d e) := by
  unfold ioapicMapPinToVector; exact mt_machineOpLift _
theorem mt_ioapicMapPinToVectorRemapped (a b c d e f : Word) : MaskT (ioapicMapPinToVectorRemapped a b c d e f) := by
  unfold ioapicMapPinToVectorRemapped; exact mt_machineOpLift _

end MaskT

/-! ## The writer leaves -/

theorem gk_doMachineOp {α : Type} {mop : NonDet MachineState α} (h : MaskT mop) :
    GK (doMachineOp (Z := Unit) mop) := fun _ L => L.msk mop h

theorem gk_updateTimeStamp : GK (updateTimeStamp (Z := Unit)) := fun _ L => L.uts

theorem gk_setIrqState (st : IrqState) (i : Irq) : GK (setIrqState (Z := Unit) st i) := fun _ L => L.sis st i

theorem gk_ack (i : Irq) : GK (doMachineOp (Z := Unit) (maskInterrupt false i)) := fun _ L => L.ack i

/-- A `MaskT` goal by the machine leaves. -/
macro "mt_auto" : tactic => `(tactic| repeat' (first
  | with_reducible exact mt_maskInterrupt_true _ | with_reducible exact mt_getActiveIRQ _ | with_reducible exact mt_ackInterrupt _
  | with_reducible exact mt_machineOpLift _ | with_reducible exact mt_storeWord _ _ | with_reducible exact mt_clearMemory _ _ | with_reducible exact mt_freeMemory _ _
  | with_reducible exact mt_of_mkf (mkf_loadWord _) | with_reducible exact mt_of_mkf (mkf_invalidateASID _ _)
  | with_reducible exact mt_of_mkf (mkf_invalidateTranslationSingleASID _ _)
  | with_reducible exact mt_of_mkf (mkf_invalidateLocalPageStructureCacheASID _ _)
  | with_reducible exact mt_of_mkf mkf_readFpuState | with_reducible exact mt_of_mkf (mkf_writeFpuState _)
  | with_reducible exact mt_of_mkf mkf_enableFpu | with_reducible exact mt_of_mkf mkf_disableFpu | with_reducible exact mt_of_mkf mkf_isFpuEnable
  | with_reducible exact mt_of_mkf mkf_getFaultAddress | with_reducible exact mt_fl4FpuToFrame _
  | with_reducible exact mt_pure _ | with_reducible exact mt_pure' _ | with_reducible exact mt_gets _
  | with_reducible exact mt_setDeadline _ | with_reducible exact mt_ackDeadlineIRQ
  | with_reducible exact mt_in8 _ | with_reducible exact mt_in16 _ | with_reducible exact mt_in32 _
  | with_reducible exact mt_out8 _ _ | with_reducible exact mt_out16 _ _ | with_reducible exact mt_out32 _ _
  | with_reducible exact mt_ioapicMapPinToVector _ _ _ _ _
  | with_reducible exact mt_ioapicMapPinToVectorRemapped _ _ _ _ _ _
  | (with_reducible refine mt_bind ?_ (fun _ => ?_)) | (with_reducible refine mt_bind' ?_ (fun _ => ?_))
  | (with_reducible apply mt_ite)))

/-- One step of a `GK` proof. -/
macro "gk_step0" : tactic => `(tactic| first
  | with_reducible exact gk_pure _ | with_reducible exact gk_pure' _ | with_reducible exact gk_fail
  | with_reducible exact gk_gets _ | with_reducible exact gk_get
  | with_reducible exact gk_assert _ | with_reducible exact gk_assertOpt _
  | with_reducible exact gk_getsThe _
  | with_reducible exact gk_selectF _ | with_reducible exact gk_select _
  | ((with_reducible apply gk_modify); intro _; exact rfl)
  | ((with_reducible apply gk_get_put); intro _; exact rfl)
  | (exact gk_get_put' (fun _ => rfl))
  | (exact gk_get_put (fun _ => rfl))
  | with_reducible exact gk_getObject _
  | with_reducible exact gk_updateTimeStamp | with_reducible exact gk_setIrqState _ _
  | with_reducible exact gk_ack _
  | with_reducible exact gk_of_mtk (mtk_performPml4Flush _)
  | ((with_reducible refine gk_doMachineOp ?_); mt_auto; done)
  | (with_reducible refine gk_bind ?_ (fun _ => ?_))
  | (with_reducible refine gk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply gk_ite) | (with_reducible apply gk_when) | (with_reducible apply gk_unless)
  | (with_reducible refine gk_maybeM (fun _ => ?_) _) | (with_reducible apply gk_liftM)
  | (with_reducible refine gk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine gk_mapMx (fun _ => ?_) _)
  | (with_reducible refine gk_mapM (fun _ => ?_) _)
  | (with_reducible refine gk_forMx (fun _ => ?_) _)
  | with_reducible exact gke_pure _ | with_reducible exact gke_returnOk _ | with_reducible exact gke_throw _
  | with_reducible exact gke_throw' _ | with_reducible exact gke_throwOpt _ _ | with_reducible exact gke_assertE _
  | (with_reducible refine gke_bind ?_ (fun _ => ?_))
  | (with_reducible apply gke_liftE) | (with_reducible apply gke_ite) | (with_reducible apply gke_whenE)
  | (with_reducible apply gke_unlessE) | (with_reducible refine gk_catch ?_ (fun _ => ?_))
  | (with_reducible refine gke_handleE ?_ (fun _ => ?_)) | (with_reducible apply gke_liftME)
  | (with_reducible refine gke_mapMEx (fun _ => ?_) _) | (with_reducible refine gke_mapME (fun _ => ?_) _)
  | (with_reducible apply gke_withoutPreemption) | (with_reducible apply gke_capFaultOnFailure)
  | (with_reducible apply gke_lookupErrorOnFailure) | (with_reducible apply gke_unifyFailure)
  | (with_reducible apply gk_emptyOnFailure) | (with_reducible apply gk_constOnFailure)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact gk_pure _)
  | (exact gk_pure _))

/-- A `GK` lemma of a spec function (extended by the generated family, one
rule per lemma). -/
syntax "gk_leaf" : tactic
macro_rules | `(tactic| gk_leaf) => `(tactic| fail "no gk_leaf")

/-- `GK` from MachFieldFamT's `MTK` family, else one step. -/
macro "gk_auto" : tactic => `(tactic| repeat' (first
  | gk_leaf
  | gk_step0
  | ((with_reducible apply gk_of_mtk); mtk_leaf; done)
  | ((with_reducible apply gke_of_mtke); mtk_leaf; done)))

end

end Fl4Proofs.P3.SInvV
