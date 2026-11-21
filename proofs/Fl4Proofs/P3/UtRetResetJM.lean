/-
P3 (DESIGN.md §9), untyped (KENTRY-PLAN mr5): **the Untyped invocation under
`MachPlat`** (mr4 NEXT (1)): UtResetLoopJM's `JAtZ.reset_loopJM` lifted
through the reset and the retype with a reset, so the Untyped decode ends in
`JAtPreMV` (what `hPre_ofZQIM` consumes) with no `PPPlat`.

* `UtRetPostJM`: XTopJointUt's `UtRetPostJ` with `JAtPreMV` after a
  preempted reset; `UtRetPostJ.toM` (an invocation whose spec side has no
  error outcome after the restart is never preempted: both posts agree);
  `NoErrAt`/`noErrAt_bind`/`noErrAt_liftE_single` (SpecNoPre's `NoErrE` at one
  state), `noErr_retypeNoReset` (the spec's retype without a reset has no error
  outcome), `noErrAt_retypeDev` (a reset of a device cap has none: l4v
  `reset_untyped_cap` clears and preempts only RAM caps).
* `JAtZ.reset_untypedJM`: UtResetTopJ's `JAtZ.reset_untypedJ` with `MachPlat`
  + `PPPlatA` + `MR`/`ValidMachineTime`/`ValidIrqMasks` at the start (the
  spec's `delete_objects` changes only the heap and memory, so the three hold
  at `delSt` by definition), the chunk loop by `JAtZ.reset_loopJM`, ending in
  `ResetJPostM`.
* `JAtZ.utResetJM`: UtRetResetJ's `JAtZ.utResetJ` likewise (the restart keeps
  the machine state, the clock and the interrupt table), ending in
  `UtRetPostJM`.
* `JUtRetHypDM`, `JAtZ.jUtRetHypM` (RAM caps: every native object type with a
  reset by `utResetJM`, without one by `JAtZ.jUtRetHyp`'s proved cases and
  `toM`), `JAtZ.jUtRetHypDevM` (device caps: `JAtZ.jUtRetHypDev` and `toM`,
  the reset of a device cap has no error outcome), and
  `decode_invocation_untypedJM` (XTopJointUt's decode, `XCapP` at
  `JAt`/`JAtPreMV`).

The native types only (`hNat`: XTopJointEntry's `JUtPath.vtx` [scope] keeps
the VT-x types 14..18 out, so UtRetResetJ's `JUtRetHypR2` [W] is not needed
here). No new premise.
-/
import Fl4Proofs.P3.UtResetLoopJM
import Fl4Proofs.P3.UtDevReset
import Fl4Proofs.P3.SpecNoPre
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec's retype: no error outcome without a RAM reset -/

namespace NoPre
open Fl4Spec

/-- No outcome of `m` from `s` is an error. -/
def NoErrAt {ε α : Type} (m : NonDetE (State Unit) ε α) (s : State Unit) : Prop :=
  ∀ y, y ∈ (m.run s).1 → ∀ e, y.1 ≠ .error e

theorem NoErrE.at {ε α : Type} {m : NonDetE (State Unit) ε α} (h : NoErrE m) (s : State Unit) : NoErrAt m s :=
  h s

theorem noErrAt_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} (hm : NoErrAt m s) (hf : ∀ x, x ∈ (m.run s).1 → ∀ a, x.1 = .ok a → NoErrAt (f a) x.2) :
    NoErrAt (m >>= f) s := by
  intro y hy e he
  change y ∈ (NonDet.bind (ExceptT.run m) _ s).1 at hy
  obtain ⟨⟨r, s1⟩, hr, hy⟩ := hy
  cases r with
  | error e' => exact hm _ hr e' rfl
  | ok a => exact hf _ hr a rfl y hy e he

theorem noErrAt_liftE_single {ε α β : Type} {m : NonDet (State Unit) α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} {a : α} (hm : m s = ({(a, s)}, False)) (hf : NoErrAt (f a) s) :
    NoErrAt (NonDetE.liftE m >>= f) s := by
  refine noErrAt_bind ((noErr_liftE m).at s) fun x hx a' ha' => ?_
  unfold NonDetE.liftE at hx
  rw [ExceptT.run_lift] at hx
  obtain ⟨z, hz, hx⟩ := hx
  rw [hm] at hz
  have hz' : z = (a, s) := hz
  subst hz'
  rw [show x = (.ok a, s) from hx] at ha' ⊢
  cases ha'
  exact hf

/-- **The spec's retype without a reset has no error outcome.** -/
theorem noErr_retypeNoReset (b c d : Bool) (sl : CslotPtr) (base rb : Word) (t : ApiObjectType) (us : Nat)
    (slots : List CslotPtr) (dev : Bool) :
    NoErrE (fl4PerformInvocation (Z := Unit) b c d (.invokeUntyped (.retype sl false base rb t us slots dev))) := by
  simp only [fl4PerformInvocation, fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true,
    ↓reduceIte, NonDetE.returnOk]
  exact noErr_bind (noErr_bind (noErr_pure _) fun _ => noErr_liftE _) fun _ => noErr_pure _

/-- **A device cap's reset has no error outcome** (no clear, no preemption
point: `resetUntypedCap`'s `dev ∨ sz < resetChunkBits` branch). -/
theorem noErrAt_resetDev {sl : CslotPtr} {σ : State Unit} {pb : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap true pb sz fi, σ)}, False)) :
    NoErrAt (resetUntypedCap (Z := Unit) sl) σ := by
  unfold resetUntypedCap
  refine noErrAt_liftE_single hg (NoErrE.at ?_ σ)
  simp only [NonDetE.returnOk, ndE_pure_bind, isDeviceUntypedCap, true_or, ↓reduceIte]
  split_ifs
  · exact noErr_pure _
  · repeat (first | exact noErr_pure _ | exact noErr_liftE _ | refine noErr_bind ?_ fun _ => ?_)

/-- **The spec's retype with a reset of a device cap has no error outcome.** -/
theorem noErrAt_retypeDev (b c d : Bool) {sl : CslotPtr} {σ : State Unit} {pb : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap true pb sz fi, σ)}, False)) (base rb : Word)
    (t : ApiObjectType) (us : Nat) (slots : List CslotPtr) (dev : Bool) :
    NoErrAt (fl4PerformInvocation (Z := Unit) b c d (.invokeUntyped (.retype sl true base rb t us slots dev))) σ := by
  simp only [fl4PerformInvocation, fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte,
    NonDetE.returnOk]
  refine noErrAt_bind (noErrAt_bind (noErrAt_resetDev hg) fun _ _ _ _ => (noErr_liftE _).at _)
    fun _ _ _ _ => (noErr_pure _).at _

end NoPre

section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **An untyped invocation's outcome at `J` under `MachPlat`**: XTopJointUt's
`UtRetPostJ` with `JAtPreMV` after a preempted reset. -/
def UtRetPostJM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (σ : Fl4Spec.State Unit)
    (blk call don : Bool) (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)).run σ1).1, (∃ th' G',
      ((res.1 = .Ok () ∧ y.1 = .ok []) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2 ∧ MdbOKV (L.ksb res.2.1) (L.mem res.2.1) G') ∧
      (if res.1 = .Err .Preempted then JAtPreMV (L := L) arI AR MR res.2.1 res.2.2 y.2
        else JAt (L := L) arI AR res.2.1 res.2.2 y.2)

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`UtRetPostJ` gives `UtRetPostJM` when the spec side cannot err** after
the restart (then FL4's outcome is not `Preempted`). -/
theorem UtRetPostJ.toM {σ : Fl4Spec.State Unit} {blk call don : Bool} {inv : Fl4Spec.UntypedInvocation}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : UtRetPostJ (L := L) arI AR σ blk call don inv res)
    (hne : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      NoPre.NoErrAt (Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)) σ1) :
    UtRetPostJM (L := L) arI AR MR σ blk call don inv res := by
  obtain ⟨σ1, hst, y, hy, hrel, hX⟩ := h
  have hok : res.1 ≠ .Err .Preempted := by
    intro hp
    obtain ⟨-, -, hc, -⟩ := hrel
    rcases hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [hp] at h1; cases h1
    · exact hne σ1 hst y hy () h2
  refine ⟨σ1, hst, y, hy, hrel, ?_⟩
  rw [if_neg hok] at hX ⊢
  exact hX

theorem utRetPostJM_of_body {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool} {inv : Fl4Spec.UntypedInvocation}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : UtBodyPost (L := L) arI AR σ1 inv res) : UtRetPostJM (L := L) arI AR MR σ blk call don inv res := by
  obtain ⟨σ', hrun, hok, ⟨th', G', hrel⟩, hJ⟩ := h
  refine ⟨σ1, hst1, (.ok [], σ'), perf_ut_mem blk call don hrun, ⟨th', G', Or.inl ⟨hok, rfl⟩, hrel⟩, ?_⟩
  rw [if_neg (by rw [hok]; simp)]
  exact hJ

theorem utRetPostJM_of_reset {σ σ1 σ2 : Fl4Spec.State Unit} {blk call don : Bool} {sl : Fl4Spec.CslotPtr}
    {base rb : Fl4Spec.Word} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hr : ((.ok (), σ2) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) sl).run σ1).1)
    (h : UtBodyPost (L := L) arI AR σ2 (.retype sl false base rb t us slots dev) res) :
    UtRetPostJM (L := L) arI AR MR σ blk call don (.retype sl true base rb t us slots dev) res := by
  obtain ⟨σ', hrun, hok, ⟨th', G', hrel⟩, hJ⟩ := h
  have hy := invoke_reset_ok Fl4Spec.fl4ObjBitsApi sl base rb t us slots dev hr (mem_of_run hrun)
  refine ⟨σ1, hst1, (.ok [], σ'), mem_bindE_ok hy (mem_returnOk []), ⟨th', G', Or.inl ⟨hok, rfl⟩, hrel⟩, ?_⟩
  rw [if_neg (by rw [hok]; simp)]
  exact hJ

theorem utRetPostJM_of_preempt {σ σ1 σ' : Fl4Spec.State Unit} {blk call don : Bool} {sl : Fl4Spec.CslotPtr}
    {base rb : Fl4Spec.Word} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hr : ((.error (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) sl).run σ1).1)
    (he : res.1 = .Err .Preempted) (hpre : JAtPreMV (L := L) arI AR MR res.2.1 res.2.2 σ') {Z' : XSets}
    (hX : XTopAt (L := L) AR Z' res.2.1 res.2.2 σ') :
    UtRetPostJM (L := L) arI AR MR σ blk call don (.retype sl true base rb t us slots dev) res := by
  obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hX.rel
  refine ⟨σ1, hst1, (.error (), σ'), mem_bindE_err (invoke_reset_err Fl4Spec.fl4ObjBitsApi sl base rb t us slots dev hr),
    ⟨Z'.th, Z'.G, Or.inr ⟨he, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ?_⟩
  rw [if_pos he]
  exact hpre

end

section ResetM
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
  {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- **FL4's `reset_untyped` at `J` under `MachPlat`** (module docstring). -/
theorem JAtZ.reset_untypedJM (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hPA : PPPlatA arI AR)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hc0 : Z.c = 0#u64) (hR0 : PPR0 σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    (hnc : ¬ ∃ y, σ.cdt y = some (pp.bv, idx)) (hfi0 : fi.val ≠ 0)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s)
    (hDT : DbgTimerKept (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) Cs s)
    (hAF : ArchFitHyp H σ)
    {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ Z.P) (hX4 : X4 ⊆ Z.L4) (hX3 : X3 ⊆ Z.L3) (hX2 : X2 ⊆ Z.L2)
    (hX1 : X1 ⊆ Z.L1) (hM : Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s) XP X4 X3 X2 X1)
    (hXc : ∀ y, IsSlot Z.th y → ∀ k q, Vs.VNeed (capV (L.mem s) y) k q → q ∈ Vs.lvlSet XP X4 X3 X2 X1 k)
    (hMR : MR a σ.machineState) (hVT : ValidMachineTime σ) (hVIM : ValidIrqMasks σ) :
    untyped.reset_untyped st arI s a (cslotAddr (pp.bv, idx)) ⦃ res =>
      ResetJPostM (L := L) arI AR MR ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
        (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs (L.ksb s) σ (L.mem s) pp idx p sb res ⦄ := by
  set x := cslotAddr (pp.bv, idx) with hxdef
  set Z' := (Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s) with hZ'
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot Z.th x := hAs.isSlot
  obtain ⟨hP, ⟨hSR, -, hML, -, -⟩, -⟩ := J.xtop.rel
  have U := J.utc _ p sb fi false hAs hcap rfl
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hfit := U.pfit
  have hxm : x ∈ Z.G.chains.flatten := (hML.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hcv : capV (L.mem s) x = .Untyped p sb fi false := capV_of_capAt hcap
  have hND : NotDev (L.mem s) x p sb fi := by unfold NotDev; rw [hcv]; simp
  have hxout := U.ns hnc x hxm
  have hppout : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ sb.val) := by
    obtain ⟨q, j, hj, hq, he⟩ := hAs.at
    have : pp = q := bv_inj hq
    subst this
    exact hj.obj_out hP U.nostr (by rw [← he]; exact hxout)
  have hpp' : Z'.th pp = some (.cnode rs) := by
    show restrictTh Z.th _ _ pp = _; rw [restrictTh_out hppout]; exact hpp
  have hpb : pp.bv ∉ regionSet p.bv sb.val := by rw [regionSet_iff _ _ _ hsb hfit]; exact hppout
  obtain ⟨cs, hk, hwf, -⟩ := hSR.cnode pp rs hpp
  have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap false p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hSR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have h16 : 16 ∣ 2 ^ sb.val := by
    have := Nat.pow_dvd_pow 2 U.sb4; simpa using this
  have hmod : ∀ d, d ∣ 2 ^ sb.val → p.val % d = 0 := by
    intro d hd; have := Nat.mod_mod_of_dvd p.val hd; rw [U.pal, Nat.zero_mod] at this; exact this.symm
  have hp8 : p.bv.toNat % 8 = 0 := hmod 8 (dvd_trans (by norm_num) h16)
  have hfib : fi.val ≤ 2 ^ sb.val := U.fiLe
  -- the spec's `delete_objects`
  obtain ⟨hSD, hcdt, horig, hrepr, hcdom, hdtime, hist, hinode, harch, hdl, hdsi, hum, hz⟩ :=
    delSt_facts p sb hsb hfit σ
  obtain ⟨⟨u, σD⟩, hyD⟩ := deleteObjects_has hp8 sb.val σ
  have hσD : σD = delSt p.bv sb.val σ := deleteObjects_delSt p sb hp8 (by have := U.sb4; omega) hsb hfit σ hyD
  subst hσD
  have J' := J.drop hres hAs hcap hnc hfi0 hKR hDT hAF hSD hcdt horig hrepr hcdom hdtime hist hinode harch hdl hdsi
    hum hXP hX4 hX3 hX2 hX1 hM hXc
  have hRC : RgClear Z' (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs (L.ksb s) p sb := J.rgClear_drop hAs hcap
  have hTh : restrictTh Z'.th p.val (p.val + 2 ^ sb.val) = Z'.th := restrictTh_idem _ _ _
  have hfr : RegionFree Z'.th p.val (p.val + 2 ^ sb.val) := RegionFree.restrict U.nostr
  have hRM : RgMiss p sb (delSt p.bv sb.val σ) := fun o ko ho => by
    by_cases hr : RgOf p sb o
    · rw [hSD.kin o hr] at ho; cases ho
    · rw [hSD.kout o hr] at ho; exact J.specOff hsb hfit hxm hcv hfib ho hr
  have hncD : ¬ ∃ y, (delSt p.bv sb.val σ).cdt y = some (pp.bv, idx) := by rw [hcdt]; exact hnc
  have hR0D : PPR0 (delSt p.bv sb.val σ) := by
    refine hR0.of_ppk ⟨hSD.cons, hSD.time, hSD.csc, fun u hu => by rw [hSD.rel] at hu; exact hu,
      fun q y n hq => ?_, fun q y hq => ?_, rfl, rfl, fun h => h, fun q x y hx hq hi => ?_, fun h => h⟩
    rotate_right
    · by_cases hr : RgOf p sb q
      · rw [hSD.kin q hr] at hq; cases hq
      · rw [hSD.kout q hr, hx] at hq; cases hq; exact Or.inl hi
    · by_cases hr : RgOf p sb q
      · rw [hSD.kin q hr] at hq; cases hq
      · rw [hSD.kout q hr] at hq; exact hq
    · by_cases hr : RgOf p sb q
      · rw [hSD.kin q hr] at hq; cases hq
      · rw [hSD.kout q hr] at hq; exact ⟨y, hq, rfl, id⟩
  have hc0' : Z'.c = 0#u64 := hc0
  have hP' : Placed Z'.th := J'.xtop.rel.1
  have hAs' : AbsSlot Z'.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp')⟩
  have hxs' : IsSlot Z'.th x := hAs'.isSlot
  have hobj : ∀ y, IsSlot Z'.th y → y.val + 32 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, kq, hq, h1, h2, -⟩ := slot_in_object hP' hy
    rcases hfr q kq hq with e | e <;> omega
  have hZf : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val) := U.zero hND
  -- FL4
  unfold untyped.reset_untyped
  rw [slot_cap_eq, hcap]
  have hfi0' : ¬ (fi = 0#u64) := fun e => hfi0 (by rw [e]; rfl)
  simp only [bind_ok, untyped.as_untyped, hfi0', ↓reduceIte]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hsm : sb < untyped.RESET_CHUNK_BITS
  · -- a small region: zero it, then the free index 0
    rw [if_pos hsm]
    have hsm' : sb.val < 16 := by rw [reset_chunk_bits_eq] at hsm; exact hsm
    have h63 : (sb &&& 63#u64).val = sb.val := by
      have : (sb &&& 63#u64).val = sb.val % 64 := by
        simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
      rw [this]; omega
    obtain ⟨i1, hi1, hv1, -⟩ := spec_exists (UScalar.ShiftLeft_spec (1#u64 : U64) (sb &&& 63#u64) _
      (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
    have hi1v : i1.val = 2 ^ sb.val := by
      rw [hv1, h63, Nat.shiftLeft_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
      exact Nat.pow_lt_pow_right (by decide) hsb
    simp only [lift, bind_ok, hi1, L.clear_free_eq]
    have hpal : P1.Aligned p := hp8
    have h8 : (2 : Nat) ^ sb.val % 8 = 0 := by obtain ⟨t, ht⟩ := h16; omega
    have J1 := J'.zeroRg hRC hc0' hfit hpal (n := i1) (by rw [hi1v]; exact h8) (le_refl _) (by rw [hi1v])
    set s1z := L.zr s p i1 with hs1z
    have hz1 : ∀ w : U64, P1.Aligned w → L.mem s1z w =
        if p.val ≤ w.val ∧ w.val < p.val + i1.val then 0#u64 else L.mem s w :=
      fun w hw => L.mem_zr s p _ w hpal (by rw [hi1v]; exact h8) (by rw [hi1v]; exact hfit) hw
    have hS1 : SlotsSame Z'.th (L.mem s) (L.mem s1z) :=
      slotsSame_out hP' (fun b hb => by have := hobj b hb; omega) (fun w hw ho => by
        rw [hz1 w hw, if_neg (by rw [hi1v]; omega)])
    have hcap1 : capAt (L.mem s1z) x = ok (.Untyped p sb fi false) := by rw [hS1.capAt hxs']; exact hcap
    have e0 : (0#u64 : U64).val = 0 := rfl
    have hZ1 : ZeroRegion (L.mem s1z) (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val) := by
      intro w hw h1 h2
      rw [e0] at h1
      rw [hz1 w hw, if_pos (by rw [hi1v]; omega)]
    obtain ⟨s2, hs2, cs2, hk2, hwf2, J2, hcap2, hks2, -, hfr2⟩ := spec_exists
      (J1.setFiJ hpp' hidx hcap1 hncD hfi0 hTh hfr hRM 0#u64 (by rw [e0]; omega) hZ1)
    rw [← hxdef] at hs2 hcap2 hfr2
    rw [hs2]
    simp only [bind_ok]
    have hZ2 : ZeroRegion (L.mem s2) p.val (p.val + 2 ^ sb.val) := by
      intro w hw h1 h2
      have := hobj x hxs'
      rw [hfr2 w hw (by omega) (by omega), hz1 w hw, if_pos (by rw [hi1v]; omega)]
    have hmem := reset_smallX hk hwf hidx hg hfi0 hp8 hpb hrcb rfl (by rw [hrcb]; exact hsm') hfit
      (by have := U.sb4; omega) hyD hz hk2 hwf2
    rw [e0] at J2
    refine (WP.spec_ok _).2 (Or.inl ⟨rfl, _, Ac, Lst, D, hmem, J2, hcap2, by rw [hks2, hs1z, L.ksb_zr], hZ2,
      hRM.setCn hk2 idx _, hncD, hR0D.setCn hk2 hwf2 hidx _, hz, fun y hy hne => by
        rw [capAt_frame2 hP' hxs' hy hne hfr2, hS1.capAt hy]⟩)
  · -- the chunked reset
    rw [if_neg hsm]
    have hsb16 : 16 ≤ sb.val := by rw [reset_chunk_bits_eq] at hsm; exact Nat.le_of_not_lt hsm
    have hC : untyped.RESET_CHUNK.val = 65536 := by rw [reset_chunk_eq]; rfl
    obtain ⟨i, hi, hiv, -⟩ := spec_exists (U64.sub_spec (x := fi) (y := 1#u64)
      (by have : (1#u64 : U64).val = 1 := rfl; rw [this]; omega))
    obtain ⟨i1, hi1, hi1v, -⟩ := spec_exists (U64.sub_spec (x := untyped.RESET_CHUNK) (y := 1#u64)
      (by have : (1#u64 : U64).val = 1 := rfl; rw [this, hC]; omega))
    rw [hi, hi1]
    simp only [bind_ok, lift]
    have hi1v' : i1.val = 65535 := by rw [hi1v, hC]; rfl
    have hov : (i &&& ~~~i1).val = (fi.val - 1) / 65536 * 65536 := by
      rw [and_not_mask i i1 hi1v', hiv]; rfl
    have hdv : 65536 ∣ 2 ^ sb.val := by
      have := Nat.pow_dvd_pow 2 hsb16; simpa using this
    obtain ⟨t, ht⟩ := hdv
    have hq : (fi.val - 1) / 65536 < t := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
    have hqa := Nat.lt_div_mul_add (a := fi.val - 1) (b := 65536) (by decide)
    have hK := reset_initX hk hwf hidx hg hfi0 hp8 hpb hrcb (by rw [hrcb]; simp; omega) hfib hyD
    rw [hrcb] at hK
    exact JAtZ.reset_loopJM hAK hA hnd hMP hPA hrcb hpp' hidx hTh hfr hRC hc0' (hmod 65536 ⟨t, ht⟩) hfit σ (L.mem s) s a
      (i &&& ~~~i1) _ Ac Lst D fi (by rw [hov]; omega) (by rw [hov, ht]; nlinarith) J' hcap hfi0
      (fun w hw h1 h2 => hZf w hw (by rw [hov] at h1; omega) h2)
      (by rw [hov, Nat.mul_div_cancel _ (by decide)]; simpa using hK) hRM hncD hR0D rfl hz (fun _ _ _ => rfl)
      (hMP.frame a _ _ hMR rfl rfl rfl rfl) hVT hVIM

end ResetM

section UtResetM
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **The retype with a reset at `J` under `MachPlat`** (module docstring). -/
theorem JAtZ.utResetJM {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64} (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r true fiv)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s)
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hPA : PPPlatA arI AR)
    (hrcb : Fl4Spec.resetChunkBits = 16)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    (hUZ : UtZero (L.mem s) Z.G σ) (hUN : UtNodesJ (L.mem s) Z.G (L.ksb s))
    (hB : UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv)
    (hMR : MR ar σ.machineState) (hVT : ValidMachineTime σ) (hVIM : ValidIrqMasks σ) (blk call don : Bool) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) true
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false) ⦃ res =>
      UtRetPostJM (L := L) arI AR MR σ blk call don (.retype (pp.bv, idx) true p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄ := by
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  obtain ⟨hP, ⟨-, -, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have hcv := capV_of_capAt hcap
  have U := J.utc _ p sb fi false hAs hcap rfl
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hfit := U.pfit
  have hnc : ¬ ∃ y, σ.cdt y = some (pp.bv, idx) := by
    have e := hctx.resetEq; exact of_decide_eq_true e.symm
  have hfiv0 : fiv = 0#u64 := by rw [hctx.fidx]; rfl
  -- the restart
  obtain ⟨s1, σ1, x1, -, hst1, hkx, hcur, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hks1, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hKN1 : UtNodesAt (L.ksb s1) p sb := by rw [hks1]; exact hUN _ hxG p sb fi hcv
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := fun o ho => by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
  have hσ1c : σ1.kheap (L.curW s).bv = some (.tcb { x1 with tcbState := .restart }) := by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp
  have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hni1 : Entered σ1 :=
    ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact J.restart_keeps_resume hni hkx hcur⟩
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hctx1 : RetCtx (L := L) Z.th s1 σ1 (pp.bv, idx) sb fi false nt us dest off win t r true fiv :=
    ⟨hctx.ty, hctx.size, ⟨hctx.cnode.1, hctx.cnode.2.1, hctx.cnode.2.2.1, by
        obtain ⟨y, rr, gs, g, hy, hcy⟩ := hctx.cnode.2.2.2
        exact ⟨y, rr, gs, g, hy, (hSS1.capAt hy).trans hcy⟩⟩, hctx.window,
      fun i h1 h2 => (hSS1.capAt ⟨dest, i, Or.inl ⟨r, hctx.cnode.1, by have := hctx.window.2.2; omega⟩, rfl⟩).trans
        (hctx.empty i h1 h2),
      by rw [hσ1cdt]; exact hctx.resetEq, hctx.fidx, hctx.sizeBits, hctx.memory, hctx.device⟩
  have hBO1 : BufObjHyp Z.B σ1 := fun wp hw => by
    obtain ⟨o, ko, hk, h1, h2⟩ := hBO wp hw
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hkx] at hk; cases hk
      exact ⟨_, _, hσ1c, h1, by simpa [Fl4Spec.objBits] using h2⟩
    · exact ⟨o, ko, by rw [hσ1k o ho]; exact hk, h1, h2⟩
  have hAF1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hσ1c] at h; cases h
    · rwa [hσ1k o ho] at h) hH
  have hnc1 : ¬ ∃ y, σ1.cdt y = some (pp.bv, idx) := by rw [hσ1cdt]; exact hnc
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 =
      ({(.untypedCap false p.bv sb.val fi.val, σ1)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J1.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp)
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  rw [hs1]; simp only [bind_ok]
  by_cases hf0 : fi.val = 0
  · -- an unused cap: the reset does nothing (`retype_reset_unused`)
    have hfi : fi = 0#u64 := UScalar.eq_of_val_eq (by rw [hf0]; rfl)
    subst hfi
    rw [retype_reset_unused arI s1 ar _ _ nt us dest off win false hcap1]
    have hU0 := invokeUntyped_reset_unused Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv
      (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false σ1 hg1
    have hRU1 : ∀ lo hi : Nat, p.val + (0#u64 : U64).val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
        KeptRefsP3 (L := L) H (RegionD H lo hi) s1 ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s1 :=
      fun lo hi h1 h2 => hRU s1 hs1 lo hi (J.free_dead hxG hcv h1 h2)
    have hms1 : σ1.machineState = σ.machineState := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
    have hZ1 : UtFreeZ σ1 (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val) := fun a h1 h2 => by
      rw [hms1]; exact hUZ _ hxG p sb _ hcv a h1 h2
    refine WP.spec_mono (hB Z H Cs Ac1 Lst1 D1 s1 ar σ1 J1 hni1 rs hpp hidx 0#u64 hcap1 hc0 true hctx1 hfiv0 hBO1
      hAF1 hRU1 hZ1 hKN1) (fun res h => ?_)
    obtain ⟨σ', hrun, hok, hrel, hJ⟩ := h
    exact utRetPostJM_of_body hst1 ⟨σ', by rw [hU0]; exact hrun, hok, hrel, hJ⟩
  -- a used cap: `reset_untyped` at the restart's state
  have hnd' : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr (pp.bv, idx)) := nodesc_of_cdt hP hC hAs hnc
  have hRD := (dead_childless J.jcov J.ut hI hxG hcv hnd').2
  obtain ⟨hKR, hDT⟩ := hRU s1 hs1 p.val (p.val + 2 ^ sb.val) (fun q k hq hr =>
    (hRD q k hq (by unfold RegionD MeetsR at hr; rw [hq] at hr; simpa using hr)).1)
  have hres1 : σ1.schedulerAction ≠ .chooseNewThread := by rw [hni1.2]; simp
  have hR0 : PPR0 σ := J.ppr0_start arI hni hRd0 hnq
  have hR01 : PPR0 σ1 := by
    rw [he1]
    have h := hR0.of_ppk (PPK.updTcbSc (y := { x1 with tcbState := .restart }) hkx rfl (hi := fun _ => Or.inr hcur.symm))
    unfold Notif.stsAct; split_ifs
    all_goals first | exact h | exact ⟨⟨h.1.1, fun u e => (by cases e), h.1.2.2⟩, h.2⟩
  have hms1' : σ1.machineState = σ.machineState := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hcT1 : σ1.curTime = σ.curTime := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have his1 : σ1.interruptStates = σ.interruptStates := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hMR1 : MR ar σ1.machineState := hms1' ▸ hMR
  have hVT1 : ValidMachineTime σ1 := by unfold ValidMachineTime; rw [hms1', hcT1]; exact hVT
  have hVI1 : ValidIrqMasks σ1 := by unfold ValidIrqMasks; rw [hms1', his1]; exact hVIM
  refine retype_reset_wp arI s1 ar _ _ nt us dest off win false
    (J1.reset_untypedJM hAK hA hnd hMP hPA hrcb hc0 hR01 hres1 hpp hidx hcap1 hnc1 hf0 hKR hDT hAF1
      J1.vsc.needR.1 J1.vsc.needR.2.1 J1.vsc.needR.2.2.1 J1.vsc.needR.2.2.2.1 J1.vsc.needR.2.2.2.2
      (hVM s1 hs1) Vs.needR_roots hMR1 hVT1 hVI1) ?_ ?_
  swap
  · intro e s2 a2 hpost
    rcases hpost with ⟨h, -⟩ | ⟨he, σ', hmem, hpre, Z', hX⟩
    · simp at h
    · exact utRetPostJM_of_preempt hst1 hmem he hpre hX
  intro s2 a2 hpost
  rcases hpost with ⟨-, σ2, Ac2, Lst2, D2, hmem, J2, hcap2, hkb2, -, -, hnc2, -, hz2, hSl2⟩ | ⟨h, -⟩
  swap
  · simp at h
  -- the spec's reset kept the entry fields and the old objects' types off the region
  have he := ent_reset (pp.bv, idx) σ1 (.ok (), σ2) hmem
  simp only [entF, Prod.mk.injEq] at he
  obtain ⟨hct2, hid2, hsa2⟩ := he
  have hni2 : Entered σ2 := ⟨by rw [hct2, hid2]; exact hni1.1, by rw [hsa2]; exact hni1.2⟩
  have hkT := reset_khT hg1 hf0 (.ok (), σ2) hmem
  have hkT' : ∀ o, (σ2.kheap o).map Fl4Spec.aType =
      if o ∈ regionSet p.bv sb.val then none else (σ1.kheap o).map Fl4Spec.aType := by
    intro o
    have e := congrFun hkT o
    simp only [khT, Fl4Spec.detype] at e
    rw [e]; split_ifs <;> rfl
  -- the source CNode, the destination CNode and the node cap's slot: off the region
  have hxout := U.ns hnc _ hxG
  have hppout : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ sb.val) := by
    obtain ⟨q, j, hj, hq, he'⟩ := hAs.at
    have : pp = q := bv_inj hq
    subst this
    exact hj.obj_out hP U.nostr (by rw [← he']; exact hxout)
  have hpp2 : restrictTh Z.th p.val (p.val + 2 ^ sb.val) pp = some (.cnode rs) := by
    rw [restrictTh_out hppout]; exact hpp
  obtain ⟨y, rr, gs, g, hy, hcy⟩ := hctx.cnode.2.2.2
  have hyG : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, hcy, by simp⟩
  have hdo := cnode_off_childless J.ut hI hxG hcv hnd' hyG (capV_of_capAt hcy)
  have hdest2 : restrictTh Z.th p.val (p.val + 2 ^ sb.val) dest = some (.cnode r) := by
    rw [restrictTh_out hdo]; exact hctx.cnode.1
  have hy2 : IsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) y := IsSlot.restrict hP U.nostr hy (U.ns hnc y hyG)
  have hyx : y ≠ cslotAddr (pp.bv, idx) := by
    rintro rfl; exact absurd (hcap.symm.trans hcy) (by simp)
  have hcapy : capAt (L.mem s2) y = ok (.CNode dest rr gs g) :=
    (hSl2 y hy2 hyx).trans ((hSS1.capAt hy).trans hcy)
  have hwin2 : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s2) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
    intro i h1 h2
    have hi : IsSlot Z.th (slotAddr dest.bv (BitVec.ofNat 64 i)) :=
      ⟨dest, i, Or.inl ⟨r, hctx.cnode.1, by have := hctx.window.2.2; omega⟩, rfl⟩
    have hi2 : IsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) (slotAddr dest.bv (BitVec.ofNat 64 i)) :=
      ⟨dest, i, Or.inl ⟨r, hdest2, by have := hctx.window.2.2; omega⟩, rfl⟩
    have hne : slotAddr dest.bv (BitVec.ofNat 64 i) ≠ cslotAddr (pp.bv, idx) := by
      intro e; have h0 := hctx.empty i h1 h2; rw [e, hcap] at h0; simp at h0
    exact (hSl2 _ hi2 hne).trans ((hSS1.capAt hi).trans (hctx.empty i h1 h2))
  have hctx2 : RetCtx (L := L) (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) s2 σ2 (pp.bv, idx) sb 0#u64 false nt us
      dest off win t r true fiv :=
    ⟨hctx.ty, hctx.size, ⟨hdest2, hctx.cnode.2.1, hctx.cnode.2.2.1, y, rr, gs, g, hy2, hcapy⟩, hctx.window, hwin2,
      (decide_eq_true hnc2).symm, by rw [hfiv0]; rfl, hctx.sizeBits, hctx.memory, hctx.device⟩
  -- the IPC-buffer words kept: in objects off the region, kept with their type
  have hBO2 : BufObjHyp (KeepB (KBOf p sb) Z.B) σ2 := by
    intro wp hw
    obtain ⟨hwB, -, hw1⟩ := hw
    obtain ⟨o, ko, hk, h1, h2⟩ := hBO1 wp hwB
    have hoff : o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
      rcases J1.sfree _ hxG p sb fi (capV_of_capAt hcap1) o ko hk with h | ⟨h3, h4⟩
      · exact h
      · exfalso; have := U.fiLe; rcases hw1 with e | e <;> omega
    have hnr : o ∉ regionSet p.bv sb.val := by
      rw [regionSet_iff' p o sb.val hsb hfit]
      have := Nat.one_le_two_pow (n := Fl4Spec.objBits ko); omega
    have e := hkT' o
    rw [if_neg hnr, hk] at e
    cases h2' : σ2.kheap o with
    | none => rw [h2'] at e; cases e
    | some ko' =>
      rw [h2'] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact ⟨o, ko', h2', h1, by rw [objBits_of_aType e]; exact h2⟩
  -- the arch objects: the old ones, `H`'s kept
  have hAF2 : ArchFitHyp (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) σ2 := by
    intro o ao n h hH
    rw [P1.Heap.drop_eq_some] at hH
    have e := hkT' o
    rw [h] at e
    split_ifs at e with hr
    · cases e
    · cases h1 : σ1.kheap o with
      | none => rw [h1] at e; cases e
      | some ko1 =>
        rw [h1] at e
        simp only [Option.map_some, Option.some.injEq] at e
        obtain ⟨ao1, rfl⟩ := aType_arch e.symm
        rw [objBits_of_aType e]; exact hAF1 o ao1 n h1 hH.2
  -- the kept references: the dropped heap has no object in the region
  have hRU2 : ∀ lo hi : Nat, p.val + (0#u64 : U64).val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) (H.drop (RegionD H p.val (p.val + 2 ^ sb.val)))
        (RegionD (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) lo hi) s2 ∧
      DbgTimerKept (L := L) (H.drop (RegionD H p.val (p.val + 2 ^ sb.val)))
        (RegionD (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) lo hi) Cs s2 := by
    intro lo hi h1 h2
    have e0 : (0#u64 : U64).val = 0 := rfl
    have hK : ∀ x, (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) x ≠ none →
        ¬ RegionD (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) lo hi x := by
      intro x hx hr
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hx
      obtain ⟨hnr, hHx⟩ := P1.Heap.drop_eq_some.1 hk
      have hr' : P1.MeetsR lo hi x.val
          (x.val + 2 ^ ((H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) x).elim 0 HKind.bits)) := hr
      have hnr' : ¬ P1.MeetsR p.val (p.val + 2 ^ sb.val) x.val (x.val + 2 ^ ((H x).elim 0 HKind.bits)) := hnr
      rw [hk] at hr'
      rw [hHx] at hnr'
      simp only [Option.elim, P1.MeetsR] at hr' hnr'
      omega
    exact ⟨⟨fun _ _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _,
      fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _⟩,
      fun _ _ _ => ⟨hK _, hK _, hK _, hK _, hK _⟩, fun _ _ => ⟨hK _, hK _, hK _⟩⟩
  have hZ2 : UtFreeZ σ2 (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val) := fun a h1 h2 => hz2 a (by
    have e0 : (0#u64 : U64).val = 0 := rfl
    omega) h2
  have hKN2 : UtNodesAt (L.ksb s2) p sb := by rw [hkb2]; exact hKN1
  exact WP.spec_mono (hB _ _ Cs Ac2 Lst2 D2 s2 a2 σ2 J2 hni2 rs hpp2 hidx 0#u64 hcap2 hc0 true hctx2 hfiv0 hBO2 hAF2
    hRU2 hZ2 hKN2) (fun res h => utRetPostJM_of_reset hst1 hmem h)


end UtResetM

/-! ## The Untyped invocation and decode under `MachPlat` -/

section Dec
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The retype after the decode under `MachPlat`** (XTopJointUt's
`JUtRetHypD` with `UtRetPostJM`). -/
def JUtRetHypDM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (th : TypedHeap) (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p sb fi : U64) (dev : Bool) (ct : U64)
    (blk call don : Bool) (argsU : List U64) : Prop :=
  ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
    argsU.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr sl) reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us
        dest off win dev) ⦃ res =>
      UtRetPostJM (L := L) arI AR MR σ blk call don (.retype sl reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev)
        res ⦄

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The retype of a RAM untyped cap under `MachPlat`** (module docstring):
a native object type (`hNat`), with a reset by `JAtZ.utResetJM`, without one
by `JAtZ.jUtRetHyp` (its residual `JUtRetHypR` is asked only with a reset or
of a non-native type: vacuous here, the decode fixes `reset` by the cap's
children, `RetCtx.resetEq`) and `UtRetPostJ.toM`. -/
theorem JAtZ.jUtRetHypM {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {sl : Fl4Spec.CslotPtr}
    (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (hc0 : Z.c = 0#u64)
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR)
    (hPA : PPPlatA arI AR) (hrcb : Fl4Spec.resetChunkBits = 16)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    (hUZ : UtZero (L.mem s) Z.G σ) (hUN : UtNodesJ (L.mem s) Z.G (L.ksb s))
    (hMR : MR ar σ.machineState) (hVT : ValidMachineTime σ) (hVIM : ValidIrqMasks σ)
    {blk call don : Bool} {argsU : List U64} (hNat : ∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val) :
    JUtRetHypDM (L := L) arI AR MR Z.th s ar σ sl p sb fi false ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx
  have hnt14 : nt.val < 14 := by
    have h19 := (objTypeOf_fl4 hctx.ty us.val).1
    rcases hNat nt hh with h | h <;> omega
  cases reset
  · have hR' : JUtRetHypR (L := L) arI AR Z.th s ar σ sl p sb fi ct blk call don argsU := by
      intro nt' us' dest' off' win' t' r' reset' fiv' hh' hctx' hcase'
      exfalso
      have e : nt' = nt := Option.some.inj (hh'.symm.trans hh)
      subst e
      have hrs : reset' = false := hctx'.resetEq.trans hctx.resetEq.symm
      subst hrs
      rcases hcase' with h | h
      · cases h
      · omega
    exact WP.spec_mono (J.jUtRetHyp hni hct hsl hcap hBO hAF hRU hc0 hUZ hUN hR' nt us dest off win t r false fiv hh hctx)
      fun res h => h.toM fun σ1 _ => (NoPre.noErr_retypeNoReset blk call don _ _ _ _ _ _ _).at σ1
  · obtain ⟨sl1, idx⟩ := sl
    obtain ⟨pp, hp1, hpp⟩ := hsl
    dsimp only at hp1 hpp
    subst hp1
    have hB : UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv := by
      rcases (show (nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨
          nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) ∨
          nt.val = 0 ∨ nt.val = 5 ∨ nt.val = 8 ∨ nt.val = 4 ∨ nt.val = 1 by omega) with
        h | h | h | h | h | h
      · exact utEp_bodyHyp (by omega)
      · exact utUt_bodyHyp h
      · exact utSc_bodyHyp h
      · exact utPm_bodyHyp h
      · exact utCn_bodyHyp h
      · exact utTcb_bodyHyp h
    exact J.utResetJM hni hct hpp rfl hcap hc0 hctx hBO hAF hRU hAK hA hnd hMP hPA hrcb hRd0 hnq hVM hUZ hUN hB
      hMR hVT hVIM blk call don

set_option maxHeartbeats 4000000 in
/-- **The retype of a device untyped cap under `MachPlat`**: UtDevReset's
`JAtZ.jUtRetHypDev` and `UtRetPostJ.toM` (without a reset, or with one: the
spec's reset of the device cap read at the restart's state has no error
outcome, `NoPre.noErrAt_retypeDev`). -/
theorem JAtZ.jUtRetHypDevM {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {sl : Fl4Spec.CslotPtr}
    (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi true))
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (hc0 : Z.c = 0#u64)
    (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ) (hGP : DevGpm (L.mem s) Z.G σ)
    (hrcb : Fl4Spec.resetChunkBits = 16)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    {blk call don : Bool} {argsU : List U64} :
    JUtRetHypDM (L := L) arI AR MR Z.th s ar σ sl p sb fi true ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx
  refine WP.spec_mono (J.jUtRetHypDev hni hct hsl hcap hBO hAF hRU hc0 hDA hDF hGP hrcb hVM nt us dest off win t r
    reset fiv hh hctx) fun res h => h.toM fun σ1 hst1 => ?_
  cases reset
  · exact (NoPre.noErr_retypeNoReset blk call don _ _ _ _ _ _ _).at σ1
  obtain ⟨sl1, idx⟩ := sl
  obtain ⟨pp, hp1, hpp⟩ := hsl
  dsimp only at hp1 hpp
  subst hp1
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  obtain ⟨hP, -, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl hpp⟩
  obtain ⟨s1, σ1', x1, -, hst1', -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have e1 : σ1 = σ1' :=
    congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj (hst1.symm.trans hst1')).1)
  subst e1
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, -, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 =
      ({(.untypedCap true p.bv sb.val fi.val, σ1)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J1.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl hpp
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  exact NoPre.noErrAt_retypeDev blk call don hg1 _ _ _ _ _ _

/-- **An untyped cap's decode at `J` under `MachPlat`** (XTopJointUt's
`decode_invocation_untypedJ` with `JUtRetHypDM`): `XCapP` at `JAt`/`JAtPreMV`. -/
theorem decode_invocation_untypedJM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (argsU : List U64)
    (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hNative : ∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p sb fi : U64) {dev : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JUtRetHypDM (L := L) arI AR MR Z.th s ar σ sl p sb fi dev ct blk call don argsU) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl)
      (.Untyped p sb fi dev) blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hX0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (untyped_decode_refines_fl4 arI Z.th s ar σ Z.G hSR hV hP hM hC hI lbl slbl hlbl length buf ct
    hct argsU hlen hargs hNative _ sl rfl hAs p sb fi dev hc extra x0 hx0 _ hex hfan
    (fun inv res => UtRetPostJM (L := L) arI AR MR σ blk call don inv res) hR) ?_
  rintro res (⟨e, e', rfl, h1, h2⟩ | ⟨inv, hrun, σ1, hst, y, hy, hrel, hx⟩)
  · exact TopPostDMX.errP ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, hX0⟩
  · exact Or.inr ⟨.invokeUntyped inv, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, y, hy, hrel, hx⟩

end Dec

end

end Fl4Proofs.P3
