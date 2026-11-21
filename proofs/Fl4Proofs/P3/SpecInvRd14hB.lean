/-
P3 (DESIGN.md §9), invariant line G1 (rd14h, rd14g handoff (3)): **`PerfF` for
SchedControl configure** (spec side only), and the interface `ArmFW` (rd14g F's
`ArmFV` with rd8c's decode fact `CfgD` at the decode's outcome).

* Configure of `p ≠ cur_sc`: rd14d's `tb_configure_ne` (`TB σ0`), `QT ct` by
  the generated family, rd14c's `perfF_tbq`.
* Configure of cur_sc (bound to ct, Restart): the refill trace of rd14g's
  note. The front (`tcb_release_remove`, `tcb_sched_dequeue`) keeps the heap
  and `cfS`; `commit_time` runs with `OffReady` and `Suff` (the Restart state's,
  from σ0's through `CW`) and `Rdy`'s `RV`: rd's `commit_cur` leaves cur_sc
  with non-empty refills whose head time is not after the current time; then
  `refill_new` (head at the current time) or `refill_update` (rd8b's
  `refillUpdate_out`: head time kept or set to the current time) with the
  decode's `MIN_REFILLS ≤ refills` (rd8c's `CfgD`): cur_sc active with a ready
  head, ct still bound to it (only cur_sc's object is rewritten):
  **`rc_configure`** gives rd8d's `RT ct` and rd8i's `CBa ct`; the tail
  (resume, reschedule / switch, badge / sporadic writes) is an `SVS` step.
  ct σ0's from rd14d's `tz_configure`. **`perfF_configure`**.
* **`ArmFW C`**, `armFW_of`, `ArmFW.or`, **`armFW_cfg`**, **`cfgD_invE`** (the
  decode fact from the shell's decode, rd8c's `okv_fl4DecodeCfgD`),
  **`perfFR_ofKW`**, **`invF_ofKW`**, **`brF_kw`** (rd8w's `BrF (QFV C)`).
-/
import Fl4Proofs.P3.SpecInvRd14hA
open Classical

namespace Fl4Proofs.P3.SInvR.A14h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f Fl4Proofs.P3.SInvR.A14g

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The refill middle -/

/-- **Rewriting cur_sc to an SC with refill max ≥ 2 and a ready head** gives `RT t ∧ CBa t`
for a thread `t` bound to it. -/
theorem rc_upd {s : State Unit} {t c : ObjRef} {z : SchedContext} {n : Nat}
    (hb : ∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext = some c) (htc : t ≠ c)
    (hm : MIN_REFILLS ≤ z.scRefillMax) (hr : (refillHd z).rTime.toNat ≤ s.curTime.toNat) :
    B8d.RT (Sched.updSc s c z n) t ∧ B8i.CBa t (Sched.updSc s c z n) := by
  have ek : (Sched.updSc s c z n).kheap t = s.kheap t := B8.updSc_other s c z n t htc
  refine ⟨fun x c' hx hc' => ?_, fun x c' hx hc' => ?_⟩
  · rw [ek] at hx
    rw [hb x hx] at hc'; cases hc'
    exact ⟨x, c, z, n, by rw [ek]; exact hx, hb x hx, kh_upd s c z n, B8.active_of_min hm, ready_of_nat hr⟩
  · rw [ek] at hx
    rw [hb x hx] at hc'; cases hc'
    exact ⟨z, n, kh_upd s c z n, B8.active_of_min hm⟩

/-- **`refill_new` / `refill_update` of cur_sc** from a state where its head is not after the time. -/
theorem rc_mid {s : State Unit} {t c : ObjRef} {y : SchedContext} {n : Nat}
    (hk : s.kheap c = some (.schedContext y n)) (hne : y.scRefills ≠ [])
    (hr : (refillHd y).rTime.toNat ≤ s.curTime.toNat)
    (hb : ∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext = some c) (htc : t ≠ c) :
    (∀ (mr : Nat) (b per : Ticks), MIN_REFILLS ≤ mr → ∀ w ∈ (refillNew (Z := Unit) c mr b per s).1,
      B8d.RT w.2 t ∧ B8i.CBa t w.2) ∧
    (∀ (per b : Ticks) (mr : Nat), MIN_REFILLS ≤ mr → ∀ w ∈ (refillUpdate (Z := Unit) c per b mr s).1,
      B8d.RT w.2 t ∧ B8i.CBa t w.2) := by
  refine ⟨fun mr b per hm w hw => ?_, fun per b mr hm w hw => ?_⟩
  · obtain ⟨z, e, -, ez, -, er⟩ := B8.refillNew_out hk mr b per hw
    rw [e]
    refine rc_upd hb htc (by rw [ez]; exact hm) ?_
    have eh : (refillHd z).rTime = s.curTime := by
      show (the z.scRefills.head?).rTime = _
      rw [er]; rfl
    exact le_of_eq (congrArg BitVec.toNat eh)
  · obtain ⟨z, e, -, ez, -, -, -, et, -, -, -⟩ := B8.refillUpdate_out hk hne per b mr hw
    rw [e]
    refine rc_upd hb htc (by rw [ez]; exact hm) ?_
    rcases et with h | h
    · rw [h]; exact hr
    · exact le_of_eq (congrArg BitVec.toNat h)

set_option maxHeartbeats 4000000 in
/-- **Configure of cur_sc (bound to ct) ends with `RT ct ∧ CBa ct`.** -/
theorem rc_configure {σ0 u : State Unit} (b per : Ticks) (mr : Nat) (badge : Badge) (flag : Data)
    (hmr : MIN_REFILLS ≤ mr) (hR : RF σ0 u) (hRd : Rdy u) (hN : SInvB.RNE u)
    (hst : ∀ y n, u.kheap σ0.curSc = some (.schedContext y n) → y.scTcb = some σ0.curThread) :
    ∀ x ∈ (invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags σ0.curSc b per mr badge flag) u).1,
      B8d.RT x.2 σ0.curThread ∧ B8i.CBa σ0.curThread x.2 := by
  have hT := hR.tb
  have hO : Sched.OffReady u := A11.offReady_kp hR.bs.off hR.kp
  have hS : Suff u := suff_cw hR.suff hT.cw hT.cf
  have ec0 : u.curSc = σ0.curSc := cf_curSc hT.cf
  intro x hx
  unfold invokeSchedControlConfigureFlags at hx
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨ez, n0, hk0⟩ := cq5_mem_getSc hz
  obtain ⟨sc, z2⟩ := z
  simp only at ez hk0; subst z2
  dsimp only at hx
  have hsc : sc.scTcb = some σ0.curThread := hst sc n0 hk0
  have hact : scActive sc = true := act_cw hR.bs hT.cw sc n0 hk0
  have hne0 : sc.scRefills ≠ [] := hN _ sc n0 hk0 (Or.inr hact)
  obtain ⟨xu, hxu⟩ := hR.ct
  have htc : σ0.curThread ≠ σ0.curSc := fun e => by rw [e, hk0] at hxu; cases hxu
  -- the tail after the refills: ct is cur_sc's TCB, so `reschedule_required` (no switch)
  have tailB : ∀ s : State Unit, s.curThread = σ0.curThread → ∀ w ∈ ((NonDet.when (sc.scTcb ≠ none) (do
        schedContextResume σ0.curSc
        let tcbPtr ← NonDet.assertOpt sc.scTcb
        let st ← getThreadState tcbPtr
        let ct ← NonDet.gets fun s : State Unit => s.curThread
        if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr))
        : SMonad Unit Unit) s).1, SVK.SVS s w.2 := by
    intro s hcs y hy
    rw [hsc] at hy
    unfold NonDet.when at hy
    rw [if_pos (Option.some_ne_none _)] at hy
    obtain ⟨d1, hd1, hy⟩ := hy
    have s1 := B8.sv_schedContextResume' σ0.curSc s d1 hd1
    have c1 := cfk_schedContextResume' _ s d1 hd1
    obtain ⟨d2, hd2, hy⟩ := hy
    obtain ⟨ed2, ed2'⟩ := cq5_mem_assertOpt hd2
    obtain ⟨d3, hd3, hy⟩ := hy
    have ed3 : d3.2 = d2.2 :=
      cq5_ro (fun _ => by unfold getThreadState; repeat' (first | ik_step0 | ik_unfold)) hd3
    obtain ⟨d4, hd4, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hd4] at hy
    dsimp only at hy
    have e3 : d3.2 = d1.2 := ed3.trans ed2'
    have eT : d3.2.curThread = σ0.curThread := by rw [e3, cf_curThread c1, hcs]
    rw [if_pos (show d2.1 = d3.2.curThread by rw [eT]; exact (Option.some.inj ed2).symm)] at hy
    have s3 : SVK.SVS d1.2 d3.2 := by rw [e3]; exact SVK.SVS.refl _
    exact (s1.trans s3).trans (SVK.sv_rescheduleRequired' d3.2 y hy)
  have tailC : SVK.SVM (do
        setScObjRef scBadgeUpdate σ0.curSc badge
        setScObjRef scSporadicUpdate σ0.curSc (testBit flag scSporadicFlag) : SMonad Unit Unit) := by
    sv_auto
    all_goals (intro _; exact ⟨rfl, rfl, rfl⟩)
  have fin : ∀ s : State Unit, s.curThread = σ0.curThread → B8d.RT s σ0.curThread ∧ B8i.CBa σ0.curThread s →
      ∀ x ∈ ((do
        NonDet.when (sc.scTcb ≠ none) (do
          schedContextResume σ0.curSc
          let tcbPtr ← NonDet.assertOpt sc.scTcb
          let st ← getThreadState tcbPtr
          let ct ← NonDet.gets fun s : State Unit => s.curThread
          if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr))
        setScObjRef scBadgeUpdate σ0.curSc badge
        setScObjRef scSporadicUpdate σ0.curSc (testBit flag scSporadicFlag) : SMonad Unit Unit) s).1,
      B8d.RT x.2 σ0.curThread ∧ B8i.CBa σ0.curThread x.2 := by
    intro s hcs h x hx
    obtain ⟨w, hw, hx⟩ := hx
    have hS : SVK.SVS s x.2 := (tailB s hcs w hw).trans (tailC w.2 x hx)
    exact ⟨B8d.rT_svs h.1 hS, B8i.cba_sv h.2 hS⟩
  -- the front and the commit
  obtain ⟨a1, ha1, hx⟩ := hx
  have p1 : ∃ y, a1.2.kheap σ0.curSc = some (.schedContext y n0) ∧ y.scRefills ≠ [] ∧
      (refillHd y).rTime.toNat ≤ a1.2.curTime.toNat ∧
      (∀ x, a1.2.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc) ∧
      a1.2.curThread = σ0.curThread := by
    rw [hsc] at ha1
    try unfold NonDet.when at ha1
    rw [if_pos (Option.some_ne_none _)] at ha1
    obtain ⟨b1, hb1, ha1⟩ := ha1
    obtain ⟨-, eb1'⟩ := cq5_mem_assertOpt hb1
    obtain ⟨b2, hb2, ha1⟩ := ha1
    obtain ⟨k2, -, c2, -, -⟩ := B8c.trr_out hb2
    obtain ⟨b3, hb3, ha1⟩ := ha1
    obtain ⟨_, -, e3⟩ := q1_tsa_out hb3
    have k3 : b3.2.kheap = u.kheap := by rw [e3]; show b2.2.kheap = u.kheap; rw [k2, eb1']
    have c3 : cfS b3.2 = cfS u := by rw [e3]; show cfS b2.2 = cfS u; rw [c2, eb1']
    obtain ⟨b4, hb4, ha1⟩ := ha1
    rw [Set.mem_singleton_iff.1 hb4] at ha1
    try dsimp only at ha1
    try unfold NonDet.when at ha1
    have ecs3 : b3.2.curSc = σ0.curSc := (cf_curSc c3).trans ec0
    rw [if_pos ecs3] at ha1
    have hk3 : b3.2.kheap b3.2.curSc = some (.schedContext sc n0) := by rw [k3, ecs3]; exact hk0
    obtain ⟨y, ey, -, -, -, -, ene, eh, -, -, -, -⟩ := commit_cur hk3 (B8c.offReady_congr hO k3 c3)
      (B8c.suff_congr hS k3 c3) (fun p y n h => hRd.2.2.2.1 p y n (by rw [← k3]; exact h)) (fun _ => hne0) ha1
    have htc3 : σ0.curThread ≠ b3.2.curSc := by rw [ecs3]; exact htc
    refine ⟨y, ?_, ene hne0, ?_, fun x hx => ?_, ?_⟩
    · rw [ey]
      show (Sched.updSc b3.2 b3.2.curSc y n0).kheap σ0.curSc = _
      rw [← ecs3]; exact kh_upd _ _ _ _
    · rw [ey]; exact eh
    · rw [ey] at hx
      change (Sched.updSc b3.2 b3.2.curSc y n0).kheap σ0.curThread = _ at hx
      rw [B8.updSc_other _ _ _ _ _ htc3, k3] at hx
      exact hT.bd x hx
    · rw [ey]
      show b3.2.curThread = σ0.curThread
      rw [cf_curThread c3, cf_curThread hT.cf]
  obtain ⟨y1, hk1, hne1, hr1, hb1, hct1⟩ := p1
  have hmid := rc_mid hk1 hne1 hr1 hb1 htc
  have cN : ∀ (s : State Unit) (mr' : Nat) (b' per' : Ticks), ∀ w ∈ (refillNew (Z := Unit) σ0.curSc mr' b' per' s).1,
      w.2.curThread = s.curThread := fun s _ _ _ w hw => cf_curThread (cfk_refillNew' _ _ _ _ s w hw)
  have cU : ∀ (s : State Unit) (per' b' : Ticks) (mr' : Nat), ∀ w ∈ (refillUpdate (Z := Unit) σ0.curSc per' b' mr' s).1,
      w.2.curThread = s.curThread := fun s _ _ _ w hw => cf_curThread (cfk_refillUpdate' _ _ _ _ s w hw)
  split at hx
  · obtain ⟨y3, hy3, hx⟩ := hx
    exact fin y3.2 ((cN _ _ _ _ y3 hy3).trans hct1) (hmid.1 _ _ _ (le_refl _) y3 hy3) x hx
  · obtain ⟨y3, hy3, hx⟩ := hx
    have e3 : y3.2 = a1.2 := cq5_ro (fun _ => by unfold getScActive; repeat' (first | ik_step0 | ik_unfold)) hy3
    try dsimp only at hx
    split at hx
    · obtain ⟨y4, hy4, hx⟩ := hx
      obtain ⟨-, e4⟩ := cq5_mem_assertOpt hy4
      obtain ⟨y5, hy5, hx⟩ := hx
      have e5 : y5.2 = y4.2 :=
        cq5_ro (fun _ => by unfold getThreadState; repeat' (first | ik_step0 | ik_unfold)) hy5
      have es : y5.2 = a1.2 := by rw [e5, e4, e3]
      try dsimp only at hx
      split at hx
      · obtain ⟨y6, hy6, hx⟩ := hx
        rw [es] at hy6
        exact fin y6.2 ((cU _ _ _ _ y6 hy6).trans hct1) (hmid.2 _ _ _ hmr y6 hy6) x hx
      · obtain ⟨y6, hy6, hx⟩ := hx
        rw [es] at hy6
        exact fin y6.2 ((cN _ _ _ _ y6 hy6).trans hct1) (hmid.1 _ _ _ hmr y6 hy6) x hx
    · obtain ⟨y4, hy4, hx⟩ := hx
      rw [e3] at hy4
      exact fin y4.2 ((cN _ _ _ _ y4 hy4).trans hct1) (hmid.1 _ _ _ hmr y4 hy4) x hx

/-! ## The arm -/

theorem perfF_configure {σ0 u : State Unit} (i : SchedControlInvocation) (hR : RF σ0 u) (hRd : Rdy u)
    (hN : SInvB.RNE u) (hst : ∀ y n, u.kheap σ0.curSc = some (.schedContext y n) → y.scTcb = some σ0.curThread)
    (hD : B8c.CfgD (.invokeSchedControl i)) : PerfF σ0 (.invokeSchedControl i) u := by
  cases i with
  | invokeSchedControlConfigureFlags p b per mr badge flag =>
  have hmr : MIN_REFILLS ≤ mr := hD.2
  by_cases hp : p = σ0.curSc
  · subst hp
    refine perfF_q fun y hy a _ => ?_
    obtain ⟨x, hx, rfl⟩ := mem_liftE_ret (m := invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags σ0.curSc b per mr badge flag)) hy
    exact ⟨(tz_configure b per mr badge flag hR.tb hst hR.ct x hx).ct,
      qth_invokeSchedControlConfigureFlags _ u hR.qt x hx, rc_configure b per mr badge flag hmr hR hRd hN hst x hx⟩
  · refine perfF_tbq hR.bs fun y hy a _ => ?_
    obtain ⟨x, hx, rfl⟩ := mem_liftE_ret (m := invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags p b per mr badge flag)) hy
    exact ⟨tb_configure_ne p b per mr badge flag hp u hR.tb x hx,
      qth_invokeSchedControlConfigureFlags _ u hR.qt x hx⟩

/-! ## The interface with the configure decode fact -/

/-- rd14g F's `ArmFV` with rd8c's `CfgD` of the decoded invocation. -/
def ArmFW (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 s : State Unit) (u : Unit × State Unit) (h0 : KHeap) (b : Fl4Invocation) (I : ObjRef), C b →
    A10.BS σ0 → Suff σ0 → σ0.curSc ≠ σ0.idleSc → NF σ0.curThread σ0 → KZ σ0 s → SInvB.BindOK (SInvB.bv h0) b →
    SInvB.BR h0 s.kheap → B8f.RB s.curThread I s → B8n.UF s → SInv.IL [s.curThread] s →
    SInvU.GapOKN (SInvU.uV s) b → B8c.CfgD b →
    u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1 → PerfF σ0 b u.2

theorem armFW_of {C : Fl4Invocation → Prop} (h : ArmFV C) : ArmFW C :=
  fun σ0 s u h0 b I hc hB hS hi hN hz ho hr hRB hF hL hG _ hu => h σ0 s u h0 b I hc hB hS hi hN hz ho hr hRB hF hL hG hu

theorem ArmFW.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmFW C1) (h2 : ArmFW C2) :
    ArmFW (fun b => C1 b ∨ C2 b) :=
  fun σ0 s u h0 b I hc hB hS hi hN hz ho hr hRB hF hL hG hD hu =>
    hc.elim (fun c => h1 σ0 s u h0 b I c hB hS hi hN hz ho hr hRB hF hL hG hD hu)
      (fun c => h2 σ0 s u h0 b I c hB hS hi hN hz ho hr hRB hF hL hG hD hu)

theorem armFW_cfg : ArmFW A14d.CovCfg := by
  intro σ0 s u h0 b I hc hB hS hi hN hz hbo hbr hRB hF hL hG hD hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have hRB' : B8f.RB σ0.curThread I u.2 := by
    rw [← et]; exact B8j.rb_restart s hRB hu
  cases b
  case invokeSchedControl i => exact perfF_configure i hR hRB'.1 hRB'.2.2.2.1.2 (scT_restart hB hz hu) hD
  all_goals exact (hc : False).elim

/-- **The decode fact** at every `ok` outcome of the shell's decode. -/
theorem cfgD_invE {fp : Bool} {cptr : CapRef} {t : ObjRef} {info : MessageInfo}
    {a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef} {s s' : State Unit} {b : Fl4Invocation}
    (h : ((.ok b, s') : Except SyscallError Fl4Invocation × State Unit) ∈ ((invE fp cptr t info a).run s).1) :
    B8c.CfgD b := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold invE at h
  (try dsimp only at h)
  change _ ∈ (NonDet.bind (ExceptT.run (NonDetE.liftE (ε := SyscallError) (getMrs (Z := Unit) t buf info))) _ s).1
    at h
  obtain ⟨⟨r, s1⟩, hr, hy⟩ := h
  obtain ⟨x, -, e⟩ := ft_mem_liftE hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact B8c.okv_fl4DecodeCfgD (w := SInvU.uV x.2) fp info.miLabel x.1 cptr sl cap ex buf x.2 rfl b s' hy

/-- **`PerfFRc` gives rd14b's `PerfFR`** for any `C` with `ArmFW C`. -/
theorem perfFR_ofKW {C : Fl4Invocation → Prop} (hA : ArmFW C) {σ0 σ : State Unit} {I : ObjRef} (hB : A10.BS σ0)
    (hS : Suff σ0) (hi : σ0.curSc ≠ σ0.idleSc) (hN : NF σ0.curThread σ0) (hz : KZ σ0 σ)
    (hRB : B8f.RB σ.curThread I σ) (hF : B8n.UF σ)
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
    have hD := cfgD_invE hb
    rw [et] at hu
    obtain ⟨h0, hok, hbr⟩ := bindOK_invE hb
    exact hA σ0 s' u h0 b I hc hB hS hi hN hz2 hok hbr hRB' hF' hL' hG hD hu
  · exact hP

/-- **`InvFc` gives rd14b's `InvF`** for any `C` with `ArmFW C`. -/
theorem invF_ofKW {C : Fl4Invocation → Prop} (hA : ArmFW C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (hi : σ.curSc ≠ σ.idleSc) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hV : VfhAll σ) (hF : B8n.UF σ) (hL : SInv.IL [σ.curThread] σ) (hN : NF σ.curThread σ) (h : InvFc C c σ) :
    InvF c σ := by
  intro v hv ht r cr hc g hg
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  obtain ⟨ec, ei⟩ := front_ci hEF hv ht
  have hi' : v.2.curSc ≠ v.2.idleSc := by rw [ec, ei]; exact hi
  obtain ⟨hRB, -⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  have hFv := B8v.uf_front hF hv ht
  have hLv := il_front hL hv ht
  have hJ := B8j.js_getCapReg r v.2 ⟨rfl, rfl, hRB⟩ g hg
  have ect : g.2.curThread = v.2.curThread := kz_curThread hJ.1
  exact perfFR_ofKW hA hB hS hi' (nf_front hN hv ht) (kz_getCapReg (V := v.2) r v.2 rfl g hg)
    (by rw [ect]; exact hJ.2.2) (B8v.uf_js hFv hJ) (by rw [ect]; exact il_js hLv hJ) (h v hv ht r cr hc g hg)

theorem brF_kw {C : Fl4Invocation → Prop} (hA : ArmFW C) :
    ∀ (c : Syscall) (σ : State Unit), A8.EF σ → QFV C c σ → InvF c σ :=
  fun _ _ hEF h => invF_ofKW hA hEF h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.1 h.1.2.2.2.2.2.2.1
    h.1.2.2.2.2.2.2.2 h.2 h.1.1

end

end Fl4Proofs.P3.SInvR.A14h
