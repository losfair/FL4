/-
P3 (DESIGN.md §9), invariant line G1 (rd14g, rd14f handoff (c)): **the `PerfF`
kit over the walk invariants, the interface `ArmFU` with its bridge, and
`PerfF` for Untyped / ASID control** (spec side only).

* **`rtc_of`**: ct's SC, if any, is cur_sc, an SC whose refills / max are σ0's
  and whose head is not after the current time: rd8d's `RT ct` and rd8i's
  `CBa ct` (rd10's `BS σ0`: cur_sc active). `rtc_dw` (rd14f C's `DW`: bound
  with `OffReady`, or unbound), `rtc_ec` (rd14d's `EC`: `cfS` kept).
* `post_svs` (the post is an `SVS ∧ cfS` step), **`perfF_q`**: an arm whose
  `ok` outcomes have ct σ0's, rd14c's `QT ct`, `RT ct` and `CBa ct` has rd14b's
  `PerfF` (rd14e's `post_st`, rd14b's `fpo_of`).
* **`ArmFU C`** (rd14g B's `ArmAKU` facts at the decode's outcome, `PerfF` at
  the Restart state), `armFU_of` (rd14c's `ArmF`), `ArmFU.or`,
  **`perfFR_ofKU`**, **`invF_ofKU`**, `QFU C c σ` (rd14c's `InvFc C` with the
  same entry facts as `QU`), **`brF_ku`**.
* `QT ct` across the Untyped / MakePool performs (`qt_deleteObjects`
  outside the region, `qt_retype` at addresses holding no object, the reset's
  chunk loop: `qt_preemptionPoint`), **`perfF_untyped`**,
  **`perfF_asidControl`**, `armFU_covU`.
-/
import Fl4Proofs.P3.SpecInvRd14gB
open Classical

namespace Fl4Proofs.P3.SInvR.A14g
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `RT ct ∧ CBa ct` -/

/-- **ct's SC, if any, is cur_sc with σ0's refills and a head not after the time.** -/
theorem rtc_of {σ0 q : State Unit} (hB : A10.BS σ0)
    (hb : ∀ x, q.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = none ∨ x.tcbSchedContext = some σ0.curSc)
    (hk : ∀ x, q.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc →
      ∃ y n, q.kheap σ0.curSc = some (.schedContext y n))
    (hw : A8.CW σ0.curSc σ0 q)
    (hO : ∀ y n, q.kheap σ0.curSc = some (.schedContext y n) → (refillHd y).rTime.toNat ≤ q.curTime.toNat) :
    B8d.RT q σ0.curThread ∧ B8i.CBa σ0.curThread q := by
  refine ⟨fun x c hx hc => ?_, fun x c hx hc => ?_⟩
  · rcases hb x hx with h | h
    · rw [h] at hc; cases hc
    · rw [h] at hc; cases hc
      obtain ⟨y, n, hy⟩ := hk x hx h
      exact ⟨x, σ0.curSc, y, n, hx, h, hy, act_cw hB hw y n hy, ready_of_nat (hO y n hy)⟩
  · rcases hb x hx with h | h
    · rw [h] at hc; cases hc
    · rw [h] at hc; cases hc
      obtain ⟨y, n, hy⟩ := hk x hx h
      exact ⟨y, n, hy, act_cw hB hw y n hy⟩

theorem rtc_dw {σ0 q : State Unit} (hB : A10.BS σ0) (h : DW σ0 q) :
    B8d.RT q σ0.curThread ∧ B8i.CBa σ0.curThread q := by
  rcases h.rf with ⟨hw, hO⟩ | ⟨-, hn⟩
  · refine rtc_of hB (fun x hx => ?_) (fun x hx _ => ?_) hw (fun y n hy => ?_)
    · rcases h.eb with ⟨hq, -⟩ | ⟨hq, -⟩
      · exact Or.inr (hq _ x hx rfl)
      · exact Or.inl (hq _ x hx rfl)
    · rcases h.eb with ⟨-, hk⟩ | ⟨hq, -⟩
      · exact hk
      · rename_i hb; rw [hq _ x hx rfl] at hb; cases hb
    · have := hO y n (by rw [h.cs]; exact hy)
      omega
  · refine ⟨fun x c hx hc => ?_, fun x c hx hc => ?_⟩
    · rw [hn.1 _ x hx rfl] at hc; cases hc
    · rw [hn.1 _ x hx rfl] at hc; cases hc

theorem rtc_ec {σ0 q : State Unit} (hB : A10.BS σ0) (h : A14d.EC σ0 q) :
    B8d.RT q σ0.curThread ∧ B8i.CBa σ0.curThread q := by
  obtain ⟨hc, hw, he⟩ := h
  have hO : Sched.OffReady q := offReady_cw hB.off hw hc
  have ecs : q.curSc = σ0.curSc := cf_curSc hc
  refine rtc_of hB (fun x hx => ?_) (fun x hx _ => ?_) hw (fun y n hy => ?_)
  · rcases he with ⟨hq, -⟩ | ⟨hq, -⟩
    · exact Or.inr (hq _ x hx rfl)
    · exact Or.inl (hq _ x hx rfl)
  · rcases he with ⟨-, hk⟩ | ⟨hq, -⟩
    · exact hk
    · rename_i hb; rw [hq _ x hx rfl] at hb; cases hb
  · have := hO y n (by rw [ecs]; exact hy)
    omega

/-! ## `PerfF` from the end facts -/

theorem post_svs {σ0 y : State Unit} (a : List Data) (hq0 : QT σ0.curThread y) :
    ∀ q ∈ (invPost false σ0.curThread a y).1, SVK.SVS y q.2 ∧ cfS q.2 = cfS y := by
  intro q hq
  obtain ⟨x0, hx0, g0⟩ := hq0
  obtain ⟨w, hw, hq'⟩ := hq
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  rw [hx0] at hx; cases hx
  dsimp only at hq'
  rcases g0 with e | e | e
  · rw [e] at hq'
    obtain ⟨u1, hu1, hq2⟩ := hq'
    exact ⟨(sv_whenReply false _ _ y u1 hu1).trans (SVK.sv_setThreadState' _ _ u1.2 q hq2),
      (cfk_setThreadState' _ _ u1.2 q hq2).trans (cfk_whenReply false _ _ y u1 hu1)⟩
  all_goals
    rw [e] at hq'
    dsimp only at hq'
    rw [Set.mem_singleton_iff.1 hq']
    exact ⟨SVK.SVS.refl _, rfl⟩

/-- **An arm whose `ok` outcomes keep ct, `QT ct`, `RT ct` and `CBa ct` has `PerfF`.** -/
theorem perfF_q {σ0 u : State Unit} {oper : Fl4Invocation}
    (h : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false true oper).run u).1, ∀ a, y.1 = .ok a →
      y.2.curThread = σ0.curThread ∧ QT σ0.curThread y.2 ∧ B8d.RT y.2 σ0.curThread ∧ B8i.CBa σ0.curThread y.2) :
    PerfF σ0 oper u := by
  intro y hy a ha q hq
  obtain ⟨et, hQ, hR, hC⟩ := h y hy a ha
  obtain ⟨x, hx, hst⟩ := post_st a hQ q hq
  obtain ⟨hS, hc⟩ := post_svs a hQ q hq
  have eq : q.2.curThread = σ0.curThread := by rw [cf_curThread hc, et]
  rw [← eq] at hx
  exact fpo_of hx hst (by rw [eq]; exact B8d.rT_svs hR hS) (by rw [eq]; exact B8i.cba_sv hC hS)

/-! ## The interface -/

/-- rd14g B's `ArmAKU` facts at the decode's outcome, `PerfF` at the Restart state. -/
def ArmFU (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 s : State Unit) (u : Unit × State Unit) (h0 : KHeap) (b : Fl4Invocation) (I : ObjRef), C b →
    A10.BS σ0 → Suff σ0 → σ0.curSc ≠ σ0.idleSc → KZ σ0 s → SInvB.BindOK (SInvB.bv h0) b →
    SInvB.BR h0 s.kheap → B8f.RB s.curThread I s → B8n.UF s → SInv.IL [s.curThread] s →
    SInvU.GapOKN (SInvU.uV s) b →
    u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1 → PerfF σ0 b u.2

theorem armFU_of {C : Fl4Invocation → Prop} (h : ArmF C) : ArmFU C :=
  fun σ0 s u _ b _ hc hB hS _ hz _ _ _ _ _ _ hu => by
    have et : s.curThread = σ0.curThread := kz_curThread hz
    exact h σ0 u.2 b hc (rf_restart hB hS hz hu)

theorem ArmFU.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmFU C1) (h2 : ArmFU C2) :
    ArmFU (fun b => C1 b ∨ C2 b) :=
  fun σ0 s u h0 b I hc hB hS hi hz ho hr hRB hF hL hG hu =>
    hc.elim (fun c => h1 σ0 s u h0 b I c hB hS hi hz ho hr hRB hF hL hG hu)
      (fun c => h2 σ0 s u h0 b I c hB hS hi hz ho hr hRB hF hL hG hu)

/-- **`PerfFRc` gives rd14b's `PerfFR`** for any `C` with `ArmFU C`. -/
theorem perfFR_ofKU {C : Fl4Invocation → Prop} (hA : ArmFU C) {σ0 σ : State Unit} {I : ObjRef} (hB : A10.BS σ0)
    (hS : Suff σ0) (hi : σ0.curSc ≠ σ0.idleSc) (hz : KZ σ0 σ) (hRB : B8f.RB σ.curThread I σ) (hF : B8n.UF σ)
    (hL : SInv.IL [σ.curThread] σ) {cptr : CapRef} (h : PerfFRc C σ0 cptr σ) : PerfFR σ0 cptr σ := by
  intro w0 hw0 a s b s' ha hb u hu
  rcases h w0 hw0 a s b s' ha hb u hu with hc | hP
  · have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
    have hz1 : KZ σ0 s := kz_invF _ _ _ w0.2 hz0 _ ha
    have hz2 : KZ σ0 s' := kz_trans hz1 (kz_invE _ _ _ _ a s rfl _ hb)
    have hJ0 : B8j.JS σ.curThread I σ σ := ⟨rfl, rfl, hRB⟩
    have hJw := B8j.js_getMessageInfo _ σ hJ0 w0 hw0
    have hJs := B8j.js_invF _ _ _ w0.2 hJw _ ha
    have hJs' := B8j.js_invE _ _ _ _ a s hJs _ hb
    have et : σ.curThread = s'.curThread := by rw [kz_curThread hz2, kz_curThread hz]
    have hRB' : B8f.RB s'.curThread I s' := by rw [← et]; exact hJs'.2.2
    have hF' : B8n.UF s' := B8v.uf_js hF hJs'
    have hL' : SInv.IL [s'.curThread] s' := by rw [← et]; exact il_js hL hJs'
    have hG := gapOKN_of hw0 ha hb
    rw [et] at hu
    obtain ⟨h0, hok, hbr⟩ := bindOK_invE hb
    exact hA σ0 s' u h0 b I hc hB hS hi hz2 hok hbr hRB' hF' hL' hG hu
  · exact hP

/-- **`InvFc` gives rd14b's `InvF`** for any `C` with `ArmFU C`. -/
theorem invF_ofKU {C : Fl4Invocation → Prop} (hA : ArmFU C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (hi : σ.curSc ≠ σ.idleSc) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hV : VfhAll σ) (hF : B8n.UF σ) (hL : SInv.IL [σ.curThread] σ) (h : InvFc C c σ) : InvF c σ := by
  intro v hv ht r cr hc g hg
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  obtain ⟨ec, ei⟩ := front_ci hEF hv ht
  have hi' : v.2.curSc ≠ v.2.idleSc := by rw [ec, ei]; exact hi
  obtain ⟨hRB, -⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  have hFv := B8v.uf_front hF hv ht
  have hLv := il_front hL hv ht
  have hJ := B8j.js_getCapReg r v.2 ⟨rfl, rfl, hRB⟩ g hg
  have ect : g.2.curThread = v.2.curThread := kz_curThread hJ.1
  exact perfFR_ofKU hA hB hS hi' (kz_getCapReg (V := v.2) r v.2 rfl g hg) (by rw [ect]; exact hJ.2.2)
    (B8v.uf_js hFv hJ) (by rw [ect]; exact il_js hLv hJ) (h v hv ht r cr hc g hg)

/-- The entry facts the `PerfF` bridge needs beside rd14c's `InvFc C`. -/
abbrev QFU (C : Fl4Invocation → Prop) (c : Syscall) (σ : State Unit) : Prop :=
  InvFc C c σ ∧ σ.curSc ≠ σ.idleSc ∧ SInvQ.T1 σ ∧ SInvQ.EB true σ ∧ SInvU.IO (fun _ => σ.idleSc) σ ∧ VfhAll σ ∧
    B8n.UF σ ∧ SInv.IL [σ.curThread] σ

/-- **rd8w's `BrF (QFU C)`** for any `ArmFU C`. -/
theorem brF_ku {C : Fl4Invocation → Prop} (hA : ArmFU C) :
    ∀ (c : Syscall) (σ : State Unit), A8.EF σ → QFU C c σ → InvF c σ :=
  fun _ _ hEF h => invF_ofKU hA hEF h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2 h.1

/-! ## `QT ct` across Untyped / MakePool -/

theorem qt_deleteObjects (t : ObjRef) (ptr : Word) (bits : Nat) (ht : t ∉ SInvU.delR ptr bits) :
    IK (QT t) (deleteObjects (Z := Unit) ptr bits) := by
  intro s hs y hy
  obtain ⟨ms, e⟩ := SInvU.deleteObjects_out hy
  obtain ⟨x, hx, g⟩ := hs
  exact ⟨x, by rw [kh_detype e ht]; exact hx, g⟩

theorem qt_retype {bA : ApiObjectType → Nat → Nat} {ptr : ObjRef} {n o : Nat} {ty : ApiObjectType}
    {dev : Bool} {t : ObjRef} {s : State Unit} (h : QT t s) (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), s.kheap q = none) :
    ∀ y ∈ (retypeRegionWith (Z := Unit) bA ptr n o ty dev s).1, QT t y.2 := by
  intro y hy
  rcases retype_mem hy with e | ⟨ob, e⟩
  · rw [e]; exact h
  · obtain ⟨x, hx, g⟩ := h
    refine ⟨x, ?_, g⟩
    rw [e]
    show (List.foldr (fun p kh => Function.update kh p (some ob)) s.kheap (SInvU.retPtrs ptr n (bA ty o))) t = _
    rw [SInvU.foldr_upd, if_neg (fun hm => by rw [hF t hm] at hx; cases hx)]
    exact hx

theorem kh_uts (K : KHeap) : IK (fun s : State Unit => s.kheap = K) (updateTimeStamp (Z := Unit)) :=
  fun _ h _ hy => (SInvO.uts_off hy).1.trans h

theorem kh_preemptionPoint (K : KHeap) : IKE (fun s : State Unit => s.kheap = K) (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE
  repeat' (first | exact kh_uts K | exact ik_doExtendedOp (fun _ _ h => h) _ |
    exact ik_doMachineOp (fun _ _ h => h) _ | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDet.when))

theorem qt_preemptionPoint (t : ObjRef) : IKE (QT t) (preemptionPoint (Z := Unit)) := by
  intro s hs y hy
  have hk := kh_preemptionPoint s.kheap s rfl y hy
  obtain ⟨x, hx, g⟩ := hs
  exact ⟨x, by rw [hk]; exact hx, g⟩

theorem qt_dmo (t : ObjRef) {α : Type} (mop : NonDet MachineState α) : IK (QT t) (doMachineOp (Z := Unit) mop) := by
  intro s hs y hy
  have hk := ik_doMachineOp (P := fun s' : State Unit => s'.kheap = s.kheap) (fun _ _ h => h) mop s rfl y hy
  obtain ⟨x, hx, g⟩ := hs
  exact ⟨x, by rw [hk]; exact hx, g⟩

set_option maxHeartbeats 4000000 in
/-- `reset_untyped_cap` of a held untyped whose region does not hold `t`. -/
theorem qt_resetUntypedCap (t : ObjRef) (sl : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ sl = some (.untypedCap dev b n fi)) (ht : t ∉ SInvU.delR b n) (hq : QT t σ) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) sl) σ).1, QT t y.2 := by
  intro y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := SInvU.run_liftE_bind_mem hy
  obtain ⟨cap, s'⟩ := x
  obtain ⟨hs, hcx⟩ := SInvU.getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := SInvU.run_returnOk_bind_mem hy
  replace hy := SInvU.run_returnOk_bind_mem hy
  dsimp only at hy
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact hq
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := SInvU.run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, Fl4Spec.objRefOf] at hz
    have hz0 : QT t z.2 := qt_deleteObjects t b n ht σ hq z hz
    refine (?_ : IKE (QT t) _) z.2 hz0 y hy
    try dsimp only
    repeat' (first | exact qt_preemptionPoint t | exact qt_dmo t _ | exact qt_of_tv t fun _ => B8d.tv_setCap _ _ | (with_reducible refine ike_mapMEx (fun _ => ?_) _) | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless) | (unfold archPostResetUntyped))

theorem qt_copyGlobalMappings (t p : ObjRef) : IK (QT t) (copyGlobalMappings (Z := Unit) p) :=
  qt_of_tv t fun _ => by unfold copyGlobalMappings storePml4e setPml4; tv_auto

theorem qt_createCap (t : ObjRef) (ty : ApiObjectType) (bits : Nat) (u : CslotPtr) (dev : Bool)
    (d : CslotPtr × ObjRef) : IK (QT t) (createCap (Z := Unit) ty bits u dev d) :=
  qt_of_tv t fun _ => by unfold createCap; tv_auto

set_option maxHeartbeats 4000000 in
/-- The retype's body keeps `QT t` (the addresses hold no object, `t` holds a TCB). -/
theorem qt_utBody (t : ObjRef) (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat)
    (slots : List CslotPtr) (dev : Bool) (σ : State Unit) (hq : QT t σ)
    (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) :
    ∀ x ∈ (do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs) : NonDet (State Unit) _) σ |>.1, QT t x.2 := by
  intro x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : QT t x4.2 := qt_of_tv t (fun _ => B8d.tv_setCap _ _) σ hq x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := qt_retype (ty := ty) (dev := dev) hb4
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) x5 hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hb6 : QT t x6.2 := by
    unfold initArchObjects at hx6
    refine (?_ : IK (QT t) _) x5.2 hb5 x6 hx6
    exact SInv.ik_when _ (SInv.ik_mapMx (fun _ => qt_copyGlobalMappings t _) _)
  exact SInv.ik_mapMx (fun d => qt_createCap t _ _ _ _ d) _ x6.2 hb6 x hx

set_option maxHeartbeats 4000000 in
/-- **`invoke_untyped` keeps `QT ct`** (ct is bound, so outside the reset's region). -/
theorem qt_fl4InvokeUntyped (ui : UntypedInvocation) {σ0 : State Unit} (σ : State Unit) (hD : DU σ0 σ)
    (hq : QT σ0.curThread σ)
    (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ) (hIt : SInvG.IdleOutV σ)
    (hB : SInvB.ScBackS σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hok : SInvU.UtRetOK σ ui) :
    ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) ui).run σ).1, QT σ0.curThread y.2 := by
  intro y hy
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := id hok
  cases reset
  · have hfr := SInvU.utRet_fresh hU.1.1 hok
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
    replace hy := SInvU.run_returnOk_bind_mem hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact qt_utBody _ s base rb ty sz slots dev σ hq hfr x hx
  · obtain ⟨xt, hxt, hbt⟩ := hD.bd
    obtain ⟨yc, nc, hyc⟩ := hD.sc
    obtain ⟨hct, -⟩ := B8n.bnd_pair hU hL hIt hO hB hc (hr rfl) _ xt _ yc nc hxt hbt hyc
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hbz := qt_resetUntypedCap _ s hc hct hq z hz
    have hfz := SInvU.utRet_fresh_after_reset hU.1.1 hok z hz
    obtain ⟨r, s1⟩ := z
    cases r with
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz
    | ok u =>
      try dsimp only at hy
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
      exact qt_utBody _ s base rb ty sz slots dev s1 hbz hfz x hx

set_option maxHeartbeats 4000000 in
/-- **MakePool keeps `QT ct`.** -/
theorem qt_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) {σ0 : State Unit} (σ : State Unit)
    (hD : DU σ0 σ) (hq : QT σ0.curThread σ)
    (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ) (hIt : SInvG.IdleOutV σ)
    (hB : SInvB.ScBackS σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hok : SInvU.MpOKN (SInvU.uV σ) (.makePool frame slot parent base)) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, QT σ0.curThread y.2 := by
  intro y hy
  obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hok
  have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  have hf : frame ∈ SInvU.delR frame page_bits := by
    obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hU.1.1.2.1 hc'
    exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
  obtain ⟨xt, hxt, hbt⟩ := hD.bd
  obtain ⟨yc, nc, hyc⟩ := hD.sc
  obtain ⟨hct, -⟩ := B8n.bnd_pair hU hL hIt hO hB hc' hk _ xt _ yc nc hxt hbt hyc
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 := qt_deleteObjects _ frame page_bits hct σ hq y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := SInvB.deleteObjects_out' h1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hf]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : QT σ0.curThread y3.2 := qt_of_tv _ (fun _ => B8d.tv_setCap _ _) y1.2 hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hmem : ∀ q ∈ SInvU.retPtrs frame 1 (objBitsApi (.archObject .asidPoolObj) 0), q = frame := by
    intro q hq
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    rw [hq]; simp [ptrAdd]
  have hb4 := qt_retype (ty := .archObject .asidPoolObj) (dev := false) hb3
    (fun q hq => by rw [hmem q hq]; exact hn3) y4 h4
  exact (qt_of_tv _ fun _ => by tv_auto) y4.2 hb4 y hy

/-! ## The arms -/

set_option maxHeartbeats 4000000 in
theorem perfF_untyped {σ0 u : State Unit} {I : ObjRef} (ui : UntypedInvocation)
    (hR : RF σ0 u) (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) (hF : B8n.UF u)
    (hok : SInvU.UtRetOK u ui) : PerfF σ0 (.invokeUntyped ui) u := by
  have hU0 := uds_rf hR hnis hRB
  obtain ⟨-, -, -, hSI, -, hIO, hI⟩ := hRB
  have hO : SInvU.IO (fun _ => u.idleSc) u := by rw [hI]; exact hIO
  have hW := du_fl4InvokeUntyped ui u hU0 hF.1 hF.2.1 hF.2.2 hSI.back hO hok
  have hQ := qt_fl4InvokeUntyped ui u hU0.1.1 hR.qt hF.1 hF.2.1 hF.2.2 hSI.back hO hok
  refine perfF_q fun y hy a ha => ?_
  simp only [fl4PerformInvocation] at hy
  obtain ⟨z, hz, ⟨a', ha', hy'⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · obtain rfl := SInvU.mem_ret_ok hy'
    have hd := (hW z hz).1
    exact ⟨hd.ct, hQ z hz, rtc_dw hR.bs hd.dw⟩
  · cases ha

set_option maxHeartbeats 4000000 in
theorem perfF_asidControl {σ0 u : State Unit} {I : ObjRef} (o : AsidControlInvocation)
    (hR : RF σ0 u) (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) (hF : B8n.UF u)
    (hok : SInvU.MpOKN (SInvU.uV u) o) :
    PerfF σ0 (.invokeArchObject (.spec (.invokeASIDControl o))) u := by
  have hU0 := uds_rf hR hnis hRB
  obtain ⟨-, -, -, hSI, -, hIO, hI⟩ := hRB
  have hO : SInvU.IO (fun _ => u.idleSc) u := by rw [hI]; exact hIO
  refine perfF_q fun y hy a ha => ?_
  cases o with
  | makePool frame slot parent base =>
    simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
    obtain ⟨z, hz, hx⟩ := hx
    have hds : DS σ0 z.2 :=
      ds_makePool frame slot parent base u ⟨hU0.1.1, hU0.2⟩ hF.1 hF.2.1 hF.2.2 hSI.back hO hok z hz
    have hq := qt_makePool frame slot parent base u hU0.1.1 hR.qt hF.1 hF.2.1 hF.2.2 hSI.back hO hok z hz
    have e := Set.mem_singleton_iff.1 hx
    rw [e]
    exact ⟨hds.1.ct, hq, rtc_dw hR.bs hds.1.dw⟩

theorem armFU_covU : ArmFU CovU := by
  intro σ0 s u h0 b I hc hB hS hi hz hbo hbr hRB hF hL hG hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have hRB' : B8f.RB σ0.curThread I u.2 := by
    rw [← et]; exact B8j.rb_restart s hRB hu
  have hF' : B8n.UF u.2 := B8n.uf_restart hF ⟨rfl, rfl, hRB⟩ hu
  have huv : SInvU.uV u.2 = SInvU.uV s := SInvU.uk_setThreadState s.curThread .restart s rfl u hu
  have hG' : SInvU.GapOKN (SInvU.uV u.2) b := by rw [huv]; exact hG
  cases b
  case invokeUntyped ui => exact perfF_untyped ui hR hi hRB' hF' (SInvU.utRetOK_of_V hG'.1)
  case invokeArchObject i =>
    cases i with
    | spec j =>
      cases j
      case invokeASIDControl o => exact perfF_asidControl o hR hi hRB' hF' hG'
      all_goals exact (hc : False).elim
    | _ => exact (hc : False).elim
  all_goals exact (hc : False).elim

end

end Fl4Proofs.P3.SInvR.A14g
