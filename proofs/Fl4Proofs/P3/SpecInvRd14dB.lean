/-
P3 (DESIGN.md §9), invariant line G1 (rd14d, KENTRY-PLAN rd14c obstacle (e)):
**SchedControl configure** (spec side only), and arms that see the `KZ` state
behind the Restart write.

* **`ArmAK C`**: every arm in `C` has `PerfA` at the Restart outcome `u` of
  a `KZ σ0` state (more than rd14c's `RF`: every TCB view and every SC object
  is σ0's); `armAK_of` (rd14c's `ArmA` gives it), `ArmAK.or`,
  **`perfR_ofK`**, **`invR_ofK`**, tops **`kcall_rdyOffK`** /
  **`kentry_rdyOffK`**.
* `scT_restart`: at `u`, cur_sc's `sc_tcb` is ct (σ0's `CurScT` and
  `ScBack` through `KZ` and the Restart write).
* The sixth end case **`TZ σ0 q`** (ct σ0's, consumed time 0, no resume,
  `CtR`): **`ss4_tz`** (OS by its second disjunct, `RCA` / `HRC` vacuous),
  **`tz_post`**; `perfA_tbz` (`TB` or `TZ` at every `ok` outcome, no error).
* **`perfA_configure`**: configure of an SC `p ≠ cur_sc` ends in `TB`
  (`tb_configure_ne`: the commit guard dead (`tb_commitGuard`), leaves
  `cp_refillNew_ne` / `cp_refillUpdate_ne` / `bl_refillNew` / `bl_refillUpdate`,
  the rest `SVM ∧ CFK` or rd14c's `tb_ik`); configure of cur_sc ends in `TZ` (`tz_configure`: commit_time
  clears the consumed time (`mkw_commitTime`), `sched_context_resume` makes
  ct released when schedulable (`sr_schedContextResume`), ct is the SC's TCB
  so `reschedule_required` runs). No decode fact (the refill max may be 0).
* `CovCfg`, `armAK_cfg`, **`C14dB := C14d ∨ CovCfg`**, **`armAK_c14dB`**.
-/
import Fl4Proofs.P3.SpecInvRd14dA
open Classical

namespace Fl4Proofs.P3.SInvR.A14d
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Arms at the Restart outcome of a `KZ` state -/

/-- Every arm in `C` has `PerfA` at the Restart outcome of a `KZ σ0` state. -/
def ArmAK (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 s : State Unit) (u : Unit × State Unit) (bl cl dn : Bool) (b : Fl4Invocation), C b → A10.BS σ0 →
    Suff σ0 → KZ σ0 s → u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1 → PerfA σ0 bl cl dn b u.2

theorem armAK_of {C : Fl4Invocation → Prop} (h : ArmA C) : ArmAK C :=
  fun σ0 s u bl cl dn b hc hB hS hz hu => h σ0 u.2 bl cl dn b hc (rf_restart hB hS hz hu)

theorem ArmAK.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmAK C1) (h2 : ArmAK C2) :
    ArmAK (fun b => C1 b ∨ C2 b) :=
  fun σ0 s u bl cl dn b hc hB hS hz hu =>
    hc.elim (fun c => h1 σ0 s u bl cl dn b c hB hS hz hu) (fun c => h2 σ0 s u bl cl dn b c hB hS hz hu)

/-- **`PerfRc` gives rd12b's `PerfR`** for any `C` with `ArmAK C`. -/
theorem perfR_ofK {C : Fl4Invocation → Prop} (hA : ArmAK C) {σ0 σ : State Unit} (hB : A10.BS σ0) (hS : Suff σ0)
    (hz : KZ σ0 σ) {calling blocking don fp : Bool} {cptr : CapRef}
    (h : PerfRc C σ0 calling blocking don fp cptr σ) : PerfR σ0 calling blocking don fp cptr σ := by
  intro w0 hw0 a s b s' ha hb u hu
  rcases h w0 hw0 a s b s' ha hb u hu with hc | hP
  · have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
    have hz1 : KZ σ0 s := kz_invF _ _ _ w0.2 hz0 _ ha
    have hz2 : KZ σ0 s' := kz_trans hz1 (kz_invE _ _ _ _ a s rfl _ hb)
    have et : σ.curThread = s'.curThread := by rw [kz_curThread hz2, kz_curThread hz]
    rw [et] at hu
    exact hA σ0 s' u blocking calling don b hc hB hS hz2 hu
  · exact hP

/-- **`InvRc` gives rd12b's `InvR`** for any `C` with `ArmAK C`. -/
theorem invR_ofK {C : Fl4Invocation → Prop} (hA : ArmAK C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (h : InvRc C c σ) : InvR c σ := by
  intro v hv ht
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  exact ⟨fun r cl bl dn hc g hg =>
      perfR_ofK hA hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).1 r cl bl dn hc g hg),
    fun r cr hc g hg =>
      perfR_ofK hA hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).2 r cr hc g hg)⟩

/-! ## The sixth end case: consumed time 0, no resume, `CtR` -/

theorem ctR_sr' {s : State Unit} (h : SR s.curThread s) : CtR s := by
  intro x hx hrun hA hn
  obtain ⟨x', c, y, n, hx', hc, hy, ha⟩ := hA
  rw [hx] at hx'; cases hx'
  exact h (Sched.schedulable_of hx hc hrun hy ha hn)

/-- The end of configuring cur_sc. -/
structure TZ (σ0 q : State Unit) : Prop where
  ct : q.curThread = σ0.curThread
  z : q.consumedTime = 0
  nr : q.schedulerAction ≠ .resumeCurThread
  ctr : CtR q

/-- **`TZ` gives `SS4`.** -/
theorem ss4_tz {σ0 q : State Unit} (h : TZ σ0 q) : A10.SS4 q :=
  ⟨Or.inr (Or.inl ⟨h.z, h.nr⟩), fun e => absurd e h.nr, h.ctr, fun e => absurd e h.nr⟩

/-- `CtR` across an `SVS ∧ cfS` step keeping the release queue and ct runnable only if it was. -/
theorem ctR_sv' {s s' : State Unit} (h : CtR s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s)
    (hr : s'.releaseQueue = s.releaseQueue)
    (ht : ∀ x, s'.kheap s'.curThread = some (.tcb x) → runnable x.tcbState = true →
      ∃ x0, s.kheap s.curThread = some (.tcb x0) ∧ runnable x0.tcbState = true) : CtR s' := by
  have et : s'.curThread = s.curThread := congrArg (fun p => p.2.2.1) hc
  intro x hx hrun hA hn
  obtain ⟨x0, hx0, hr0⟩ := ht x hx hrun
  rw [et] at hA hn ⊢; rw [hr] at hn
  exact rdyT_svs (h x0 hx0 hr0 (A8.actB_svs_back hA hS) hn) hS

theorem kf_tcb {ct : ObjRef} {s s' : State Unit} (e : MidRun.ctV ct s' = MidRun.ctV ct s) {x : Tcb}
    (hx : s'.kheap ct = some (.tcb x)) : ∃ x0, s.kheap ct = some (.tcb x0) ∧ x0.tcbState = x.tcbState := by
  have e2 : MidRun.tsV (s.kheap ct) = some (x.tcbState, x.tcbFault) := by
    have := congrArg Prod.snd e
    simp only [MidRun.ctV] at this
    rw [← this, hx]; rfl
  cases h0 : s.kheap ct with
  | none => rw [h0] at e2; cases e2
  | some o =>
    cases o with
    | tcb x0 =>
      rw [h0] at e2
      simp only [MidRun.tsV, Option.some.injEq, Prod.mk.injEq] at e2
      exact ⟨x0, rfl, e2.1⟩
    | _ => rw [h0] at e2; cases e2

theorem kf_whenReply (ct : ObjRef) (calling : Bool) (t : ObjRef) (x : Data × List Data) :
    MidRun.KF ct (NonDet.when calling (replyFromKernel (Z := Unit) t x)) := by
  unfold NonDet.when; split
  · exact MidRun.kf_replyFromKernel' (ct := ct) t x
  · intro σ y hy; rw [Set.mem_singleton_iff.1 hy]

theorem rq_whenReply (calling : Bool) (t : ObjRef) (x : Data × List Data) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (NonDet.when calling (replyFromKernel (Z := Unit) t x)) := by
  unfold replyFromKernel; repeat' (first | ik_step0 | ik_unfold)

theorem rq_setThreadState (t : ObjRef) (ts : ThreadState) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct; repeat' (first | ik_step0 | ik_unfold)

theorem rq_rescheduleRequired (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; repeat' (first | ik_step0 | ik_unfold)

theorem nres_svs {s s' : State Unit} (h : s.schedulerAction ≠ .resumeCurThread) (hS : SVK.SVS s s') :
    s'.schedulerAction ≠ .resumeCurThread := by
  rcases hS.2.2 with e | e
  · rw [e]; exact h
  · rw [e]; intro h'; cases h'

/-- **The post keeps `TZ`.** -/
theorem tz_post (calling : Bool) (reply : List Data) {σ0 s : State Unit} (h : TZ σ0 s) :
    ∀ y ∈ (invPost calling σ0.curThread reply s).1, TZ σ0 y.2 := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  dsimp only at hy
  revert hy
  generalize hst : x.tcbState = st
  cases st <;> intro hy
  case restart =>
    obtain ⟨u, hu, hy⟩ := hy
    have s1 := sv_whenReply calling _ _ s u hu
    have c1 := cfk_whenReply calling _ _ s u hu
    have r1 : u.2.releaseQueue = s.releaseQueue := rq_whenReply calling _ _ _ s rfl u hu
    have k1 := kf_whenReply σ0.curThread calling _ _ s u hu
    have et1 : u.2.curThread = σ0.curThread := (cf_curThread c1).trans h.ct
    have t1 : CtR u.2 := ctR_sv' h.ctr s1 c1 r1 (fun x' hx' hr' => by
      rw [et1] at hx'
      obtain ⟨x0, hx0, e0⟩ := kf_tcb k1 hx'
      exact ⟨x0, by rw [h.ct]; exact hx0, by rw [e0]; exact hr'⟩)
    have s2 := SVK.sv_setThreadState' _ _ u.2 y hy
    have c2 := cfk_setThreadState' _ _ u.2 y hy
    have r2 : y.2.releaseQueue = u.2.releaseQueue := rq_setThreadState _ _ _ u.2 rfl y hy
    refine ⟨(cf_curThread c2).trans et1, (congrArg (fun p => p.1) c2).trans
      ((congrArg (fun p => p.1) c1).trans h.z), nres_svs (nres_svs h.nr s1) s2, ctR_sv' t1 s2 c2 r2 ?_⟩
    intro _ _ _
    obtain ⟨x1, hx1, e1⟩ := kf_tcb k1.symm hx
    refine ⟨x1, by rw [et1]; exact hx1, ?_⟩
    rw [e1, hst]; rfl
  all_goals (rw [Set.mem_singleton_iff.1 hy]; exact h)

/-- **An arm with `TB` or `TZ` at every `ok` outcome and no error outcome.** -/
theorem perfA_tbz {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation} (hB : A10.BS σ0)
    (hS : Suff σ0)
    (h : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don oper).run s).1,
      (∀ a, y.1 = .ok a → TB σ0 y.2 ∨ TZ σ0 y.2) ∧ ∀ e, y.1 ≠ .error e) :
    PerfA σ0 bl call don oper s := by
  intro y hy
  refine ⟨fun a ha => Or.inr fun q hq hc => ?_, fun e he => absurd he ((h y hy).2 e)⟩
  rcases (h y hy).1 a ha with ht | hz
  · exact ss4_tb hB hS (tb_post call a ht q hq) hc
  · exact ss4_tz (tz_post call a hz q hq)

theorem mem_liftE_ret {ε α β : Type} {m : NonDet (State Unit) α} {b : β} {s : State Unit}
    {y : Except ε β × State Unit}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m >>= fun _ => NonDetE.returnOk b).run s).1) :
    ∃ x ∈ (m s).1, y = (.ok b, x.2) := by
  change y ∈ (NonDet.bind (ExceptT.run (NonDetE.liftE (ε := ε) m)) _ s).1 at h
  obtain ⟨⟨r, s1⟩, hr, hy⟩ := h
  obtain ⟨x, hx, e⟩ := ft_mem_liftE hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨x, hx, show y = (.ok b, x.2) from hy⟩

/-! ## The Restart state's binding of cur_sc -/

/-- **At the Restart outcome, cur_sc's `sc_tcb` is ct.** -/
theorem scT_restart {σ0 s : State Unit} (hB : A10.BS σ0) (hz : KZ σ0 s) {u : Unit × State Unit}
    (hu : u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1) :
    ∀ y n, u.2.kheap σ0.curSc = some (.schedContext y n) → y.scTcb = some σ0.curThread := by
  intro y n hy
  obtain ⟨y0, hy0, e0⟩ := B8.scTcb_svs (SVK.sv_setThreadState' _ _ s u hu) hy
  obtain ⟨xt, hxt, -⟩ := hB.ct
  obtain ⟨y1, k, hy1, hyt, -⟩ := hB.sc.1.1 σ0.curThread xt σ0.curSc hxt (hB.cs xt hxt)
  have e := (kz_parts hz).2.1 σ0.curSc
  rw [hy0, hy1] at e
  simp only [scO, Option.some.injEq, Prod.mk.injEq] at e
  rw [← e0, e.1, hyt]

/-- The binding of `t` and `c` at `u`, read through sb2's binding frame from `u`. -/
theorem bind_br {t c : ObjRef} {u s : State Unit} (hb : SInvB.BR u.kheap s.kheap)
    (ht : ∀ x, u.kheap t = some (.tcb x) → x.tcbSchedContext = some c)
    (hst : ∀ y n, u.kheap c = some (.schedContext y n) → y.scTcb = some t) :
    (∀ y n, s.kheap c = some (.schedContext y n) → y.scTcb = some t) ∧
    (∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext = some c) := by
  refine ⟨fun y n hy => ?_, fun x hx => ?_⟩
  · obtain ⟨y0, n0, hy0⟩ := hb.sc' c y n hy
    obtain ⟨y1, n1, hy1, k1⟩ := hb.sc c y0 n0 hy0
    rw [hy] at hy1; cases hy1
    rw [k1.1]; exact hst y0 n0 hy0
  · obtain ⟨x0, hx0⟩ := hb.tcb' t x hx
    obtain ⟨x1, hx1, e1⟩ := hb.tcb t x0 hx0
    rw [hx] at hx1; cases hx1
    rw [e1]; exact ht x0 hx0

/-! ## Configure of an SC other than cur_sc -/

theorem cp_refillNew_ne (p : ObjRef) (mr : Nat) (b per : Ticks) {c : ObjRef} (hp : p ≠ c) (σ0 : State Unit) :
    IK (A8.CP σ0 c) (refillNew (Z := Unit) p mr b per) := by
  unfold refillNew maybeAddEmptyTail isRoundRobin getRefillHead refillAddTail
  repeat' (first | exact A8.cp_updateSchedContext_ne _ _ hp σ0 | cp_leaf | ik_step0)

theorem cp_refillUpdate_ne (p : ObjRef) (per b : Ticks) (mr : Nat) {c : ObjRef} (hp : p ≠ c) (σ0 : State Unit) :
    IK (A8.CP σ0 c) (refillUpdate (Z := Unit) p per b mr) := by
  unfold refillUpdate maybeAddEmptyTail isRoundRobin getRefillHead refillAddTail updateRefillHd getScRefillReady
  repeat' (first | exact A8.cp_updateSchedContext_ne _ _ hp σ0 | cp_leaf | ik_step0)

theorem tb_commitGuard {σ0 : State Unit} {p : ObjRef} (hp : p ≠ σ0.curSc) :
    IK (TB σ0) (do
      let cs ← NonDet.gets (fun s : State Unit => s.curSc)
      NonDet.when (cs = p) (commitTime (Z := Unit))) := by
  refine ik_gets_bind fun s hs y hy => ?_
  have e : s.curSc = σ0.curSc := cf_curSc hs.cf
  try dsimp only at hy
  unfold NonDet.when at hy
  rw [if_neg (by rw [e]; exact fun h => hp h.symm)] at hy
  rw [Set.mem_singleton_iff.1 hy]; exact hs

theorem bl_refillNew (t c p : ObjRef) (mr : Nat) (b per : Ticks) :
    IK (BL t c) (refillNew (Z := Unit) p mr b per) :=
  SInv.ik_and (by unfold refillNew; qb_auto) (by unfold refillNew; ks_auto)

theorem bl_refillUpdate (t c p : ObjRef) (per b : Ticks) (mr : Nat) :
    IK (BL t c) (refillUpdate (Z := Unit) p per b mr) :=
  SInv.ik_and (by unfold refillUpdate; qb_auto) (by unfold refillUpdate; ks_auto)

set_option maxHeartbeats 2000000 in
/-- **Configure of `p ≠ cur_sc` keeps `TB σ0`.** -/
theorem tb_configure_ne {σ0 : State Unit} (p : ObjRef) (b per : Ticks) (mr : Nat) (badge : Badge) (flag : Data)
    (hp : p ≠ σ0.curSc) :
    IK (TB σ0) (invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags p b per mr badge flag)) := by
  unfold invokeSchedControlConfigureFlags getScActive
  dsimp only
  repeat' (first
    | exact tb_commitGuard hp
    | exact tb_ik (cfk_refillNew' _ _ _ _) (cp_refillNew_ne _ _ _ _ hp _) (bl_refillNew _ _ _ _ _ _)
    | exact tb_ik (cfk_refillUpdate' _ _ _ _) (cp_refillUpdate_ne _ _ _ _ hp _) (bl_refillUpdate _ _ _ _ _ _)
    | exact tb_ik (cfk_schedContextResume' _) (A8.cp_schedContextResume _ _ _) (bl_of_nks (nks_schedContextResume _))
    | exact tb_ik (cfk_possibleSwitchTo' _) (A8.cp_possibleSwitchTo _ _ _) (bl_possibleSwitchTo _ _ _)
    | (with_reducible refine ik_bind ?_ (fun _ => ?_))
    | (with_reducible apply ik_when) | (with_reducible apply ik_ite)
    | with_reducible exact ik_pure _ | with_reducible exact ik_gets _ | with_reducible exact ik_assertOpt _
    | with_reducible exact ik_getsThe _
    | split
    | (refine tb_svm ?_ ?_ <;> first | (sv_auto; done) | (cfk_auto; done)))

/-! ## Configure of cur_sc -/

/-- Along configure of cur_sc, before the resume. -/
abbrev PC (t c : ObjRef) (h0 : KHeap) (s : State Unit) : Prop :=
  s.curThread = t ∧ s.curSc = c ∧ SInvB.BRs h0 s

theorem pc_of {t c : ObjRef} {h0 : KHeap} {α : Type} {m : NonDet (State Unit) α} (h1 : CFK m)
    (h2 : ∀ h0, SInvB.SBK h0 m) : IK (PC t c h0) m := by
  intro s hs y hy
  have e := h1 s y hy
  obtain ⟨et, ec, hb⟩ := hs
  exact ⟨(cf_curThread e).trans et, (cf_curSc e).trans ec, SInvB.BR.trans hb (h2 s.kheap s (SInvB.BR.refl _) y hy)⟩

theorem pcz_of {t c : ObjRef} {h0 : KHeap} {α : Type} {m : NonDet (State Unit) α} (h1 : CFK m)
    (h2 : ∀ h0, SInvB.SBK h0 m) : IK (fun s => PC t c h0 s ∧ s.consumedTime = 0) m :=
  fun s hs y hy => ⟨pc_of h1 h2 s hs.1 y hy, (congrArg (fun p => p.1) (h1 s y hy)).trans hs.2⟩

macro "pcz_auto" : tactic => `(tactic| repeat' (first
  | (refine pcz_of ?_ ?_ <;> first | (cfk_auto; done) | (intro _; sb_auto; done))
  | (with_reducible refine ik_bind ?_ (fun _ => ?_))
  | ik_step0))

/-- **`commit_time`** from a state where ct is a TCB bound to cur_sc: ct and cur_sc kept,
the consumed time cleared, sb2's binding frame. -/
theorem commit_pc {s : State Unit} {y : Unit × State Unit}
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    (hct : ∃ x, s.kheap s.curThread = some (.tcb x)) (hy : y ∈ (commitTime (Z := Unit) s).1) :
    y.2.curThread = s.curThread ∧ y.2.curSc = s.curSc ∧ y.2.consumedTime = 0 ∧ SInvB.BR s.kheap y.2.kheap := by
  have hbr : SInvB.BR s.kheap y.2.kheap := SInvB.sb_commitTime (h0 := s.kheap) s (SInvB.BR.refl _) y hy
  have k := MidRun.kf_commitTime' (ct := s.curThread) s y hy
  have et : y.2.curThread = s.curThread := congrArg Prod.fst k
  have hcs := cs_commitTime some s hb y hy
  obtain ⟨x, hx⟩ := hct
  obtain ⟨x', hx', ex⟩ := hbr.tcb _ x hx
  have h1 := hcs x' (by rw [et]; exact hx')
  rw [ex, hb x hx] at h1
  refine ⟨et, (Option.some.inj h1).symm, ?_, hbr⟩
  rw [commitTime_eq] at hy
  obtain ⟨z, -, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]

/-- An SC update keeping refills, max and TCB keeps `TZ`. -/
theorem tz_updSc {σ0 : State Unit} (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefills = y.scRefills ∧ (f y).scRefillMax = y.scRefillMax ∧ (f y).scTcb = y.scTcb) :
    IK (TZ σ0) (updateSchedContext (Z := Unit) q f) := by
  intro s h y hy
  have hS := SVK.sv_updateSchedContext q f hf s y hy
  have hc := cfk_updateSchedContext' q f s y hy
  obtain ⟨y0, n0, hk0, e⟩ := SInvB.mem_updateSchedContext hy
  refine ⟨(cf_curThread hc).trans h.ct, (congrArg (fun p => p.1) hc).trans h.z, ?_,
    ctR_sv' h.ctr hS hc (by rw [e]) ?_⟩
  · show y.2.schedulerAction ≠ _
    rw [e]; exact h.nr
  · intro x hx hr
    rw [e] at hx
    dsimp only at hx
    by_cases eq : s.curThread = q
    · rw [eq, Function.update_self] at hx; cases hx
    · rw [Function.update_of_ne eq] at hx; exact ⟨x, hx, hr⟩

set_option maxHeartbeats 4000000 in
/-- **Configure of cur_sc (bound to ct) ends in `TZ`.** -/
theorem tz_configure {σ0 u : State Unit} (b per : Ticks) (mr : Nat) (badge : Badge) (flag : Data)
    (hT : TB σ0 u) (hst : ∀ y n, u.kheap σ0.curSc = some (.schedContext y n) → y.scTcb = some σ0.curThread)
    (hct : ∃ x, u.kheap σ0.curThread = some (.tcb x)) :
    ∀ x ∈ (invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags σ0.curSc b per mr badge flag) u).1, TZ σ0 x.2 := by
  intro x hx
  unfold invokeSchedControlConfigureFlags at hx
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨ez, n0, hk0⟩ := cq5_mem_getSc hz
  obtain ⟨sc, z2⟩ := z
  simp only at ez hk0; subst z2
  dsimp only at hx
  have hsc : sc.scTcb = some σ0.curThread := hst sc n0 hk0
  have et0 : u.curThread = σ0.curThread := cf_curThread hT.cf
  have ec0 : u.curSc = σ0.curSc := cf_curSc hT.cf
  -- the tail after the refills: the resume, the reschedule, the two SC writes
  have tail : SInvB.HK (fun s => PC σ0.curThread σ0.curSc u.kheap s ∧ s.consumedTime = 0) (TZ σ0) (do
        NonDet.when (sc.scTcb ≠ none) (do
          schedContextResume σ0.curSc
          let tcbPtr ← NonDet.assertOpt sc.scTcb
          let st ← getThreadState tcbPtr
          let ct ← NonDet.gets fun s : State Unit => s.curThread
          if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr))
        setScObjRef scBadgeUpdate σ0.curSc badge
        setScObjRef scSporadicUpdate σ0.curSc (testBit flag scSporadicFlag) : SMonad Unit Unit) := by
    refine SInvB.hk_bind (Q := TZ σ0) ?_ fun _ => ?_
    · intro s hs y hy
      obtain ⟨⟨et, ec, hb⟩, hz⟩ := hs
      rw [hsc] at hy
      unfold NonDet.when at hy
      rw [if_pos (Option.some_ne_none _)] at hy
      obtain ⟨d1, hd1, hy⟩ := hy
      obtain ⟨bp, bb⟩ := bind_br hb hT.bd hst
      have sr1 : SR σ0.curThread d1.2 := sr_schedContextResume σ0.curSc σ0.curThread s bp bb hd1
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
      have eT : d3.2.curThread = σ0.curThread := by rw [e3, cf_curThread c1, et]
      rw [if_pos (show d2.1 = d3.2.curThread by rw [eT]; exact (Option.some.inj ed2).symm)] at hy
      have sr3 : SR d3.2.curThread d3.2 := by rw [eT, e3]; exact sr1
      have cy := cfk_rescheduleRequired' d3.2 y hy
      have c3 : cfS d3.2 = cfS s := by rw [e3]; exact c1
      refine ⟨(cf_curThread cy).trans eT, (congrArg (fun p => p.1) (cy.trans c3)).trans hz, ?_,
        ctR_sv' (ctR_sr' sr3) (SVK.sv_rescheduleRequired' d3.2 y hy) cy
          (rq_rescheduleRequired _ d3.2 rfl y hy) ?_⟩
      · rw [rescheduleRequired_cn d3.2 y hy]; intro h'; cases h'
      · intro x hx hr
        have k := MidRun.kf_rescheduleRequired' (ct := d3.2.curThread) d3.2 y hy
        rw [cf_curThread cy] at hx
        obtain ⟨x0, hx0, e0⟩ := kf_tcb k hx
        exact ⟨x0, hx0, by rw [e0]; exact hr⟩
    refine SInvB.hk_bind (Q := TZ σ0) (SInvB.hk_of_ik (tz_updSc _ _ fun _ => ⟨rfl, rfl, rfl⟩)) fun _ => ?_
    exact SInvB.hk_of_ik (tz_updSc _ _ fun _ => ⟨rfl, rfl, rfl⟩)
  -- the commit
  obtain ⟨a1, ha1, hx⟩ := hx
  have p1 : PC σ0.curThread σ0.curSc u.kheap a1.2 ∧ a1.2.consumedTime = 0 := by
    rw [hsc] at ha1
    try unfold NonDet.when at ha1
    rw [if_pos (Option.some_ne_none _)] at ha1
    obtain ⟨b1, hb1, ha1⟩ := ha1
    obtain ⟨eb1, eb1'⟩ := cq5_mem_assertOpt hb1
    have q1 : PC σ0.curThread σ0.curSc u.kheap b1.2 := by
      rw [eb1']; exact ⟨et0, ec0, SInvB.BR.refl _⟩
    obtain ⟨b2, hb2, ha1⟩ := ha1
    have q2 := (pc_of (cfk_tcbReleaseRemove' _) (fun _ => SInvB.sb_tcbReleaseRemove _)) b1.2 q1 b2 hb2
    obtain ⟨b3, hb3, ha1⟩ := ha1
    have q3 := (pc_of (cfk_tcbSchedAction' _ _) (fun _ => SInvB.sb_tcbSchedAction _ _)) b2.2 q2 b3 hb3
    obtain ⟨b4, hb4, ha1⟩ := ha1
    rw [Set.mem_singleton_iff.1 hb4] at ha1
    try dsimp only at ha1
    try unfold NonDet.when at ha1
    rw [if_pos q3.2.1] at ha1
    have hb3 := (bind_br q3.2.2 hT.bd hst).2
    obtain ⟨xu, hxu⟩ := hct
    obtain ⟨x3, hx3, -⟩ := (show SInvB.BR u.kheap b3.2.kheap from q3.2.2).tcb _ xu hxu
    obtain ⟨c1, c2, c3, c4⟩ := commit_pc (s := b3.2) (by rw [q3.1, q3.2.1]; exact hb3)
      ⟨x3, by rw [q3.1]; exact hx3⟩ ha1
    exact ⟨⟨c1.trans q3.1, c2.trans q3.2.1, SInvB.BR.trans q3.2.2 c4⟩, c3⟩
  try dsimp only at hx
  have pN : ∀ (mr' : Nat) (b' per' : Ticks), IK (fun s => PC σ0.curThread σ0.curSc u.kheap s ∧ s.consumedTime = 0)
      (refillNew (Z := Unit) σ0.curSc mr' b' per') :=
    fun _ _ _ => pcz_of (cfk_refillNew' _ _ _ _) (fun _ => SInvB.sb_refillNew _ _ _ _)
  have pU : ∀ (per' b' : Ticks) (mr' : Nat), IK (fun s => PC σ0.curThread σ0.curSc u.kheap s ∧ s.consumedTime = 0)
      (refillUpdate (Z := Unit) σ0.curSc per' b' mr') :=
    fun _ _ _ => pcz_of (cfk_refillUpdate' _ _ _ _) (fun _ => SInvB.sb_refillUpdate _ _ _ _)
  split at hx
  · obtain ⟨y3, hy3, hx⟩ := hx
    exact tail y3.2 (pN _ _ _ a1.2 p1 y3 hy3) x hx
  · obtain ⟨y3, hy3, hx⟩ := hx
    have p3 := (pcz_of (cfk_getScActive' _) (fun _ => by unfold getScActive; sb_auto)) a1.2 p1 y3 hy3
    try dsimp only at hx
    split at hx
    · obtain ⟨y4, hy4, hx⟩ := hx
      obtain ⟨-, e4⟩ := cq5_mem_assertOpt hy4
      obtain ⟨y5, hy5, hx⟩ := hx
      have p5 := (pcz_of (cfk_getThreadState' _) (fun _ => SInvB.sb_getThreadState _)) y4.2 (by rw [e4]; exact p3)
        y5 hy5
      try dsimp only at hx
      split at hx
      · obtain ⟨y6, hy6, hx⟩ := hx
        exact tail y6.2 (pU _ _ _ y5.2 p5 y6 hy6) x hx
      · obtain ⟨y6, hy6, hx⟩ := hx
        exact tail y6.2 (pN _ _ _ y5.2 p5 y6 hy6) x hx
    · obtain ⟨y4, hy4, hx⟩ := hx
      exact tail y4.2 (pN _ _ _ y3.2 p3 y4 hy4) x hx


/-! ## The arm -/

theorem perfA_configure {σ0 u : State Unit} (bl call don : Bool) (i : SchedControlInvocation) (hB : A10.BS σ0)
    (hS : Suff σ0) (hT : TB σ0 u)
    (hst : ∀ y n, u.kheap σ0.curSc = some (.schedContext y n) → y.scTcb = some σ0.curThread)
    (hct : ∃ x, u.kheap σ0.curThread = some (.tcb x)) :
    PerfA σ0 bl call don (.invokeSchedControl i) u := by
  cases i with
  | invokeSchedControlConfigureFlags p b per mr badge flag =>
  refine perfA_tbz hB hS fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := mem_liftE_ret (m := invokeSchedControlConfigureFlags (Z := Unit)
    (.invokeSchedControlConfigureFlags p b per mr badge flag)) hy
  refine ⟨fun a _ => ?_, fun e he => by cases he⟩
  by_cases hp : p = σ0.curSc
  · subst hp; exact Or.inr (tz_configure b per mr badge flag hT hst hct x hx)
  · exact Or.inl (tb_configure_ne p b per mr badge flag hp u hT x hx)

def CovCfg : Fl4Invocation → Prop
  | .invokeSchedControl _ => True
  | _ => False

theorem armAK_cfg : ArmAK CovCfg := by
  intro σ0 s u bl cl dn b hc hB hS hz hu
  cases b
  case invokeSchedControl i =>
    exact perfA_configure bl cl dn i hB hS (rf_restart hB hS hz hu).tb (scT_restart hB hz hu)
      (rf_restart hB hS hz hu).ct
  all_goals exact (hc : False).elim

/-- rd14d's arms so far. -/
def C14dB (b : Fl4Invocation) : Prop := C14d b ∨ CovCfg b

theorem armAK_c14dB : ArmAK C14dB := (armAK_of armA_c14d).or armAK_cfg

/-! ## The tops over any `ArmAK` set -/

section Q
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

/-- **rd12b's `kcall_rdyOff4r` with `InvRc C`** for any covered set `C`
with `ArmAK C`. -/
theorem kcall_rdyOffK {C : Fl4Invocation → Prop} (hA : ArmAK C) (hnd : numDomains = 1) (rep : Bool) (ev : Event)
    (σ : State Unit) {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → InvRc C c σ)
    (hRT : ∀ c, ev = .syscallEvent c → RecvT rep c σ)
    (hOsR : ∀ c, ev = .syscallEvent c → RecvC c → A9.OsBody rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kcall_rdyOff4r hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB
    (fun c e => invR_ofK hA (hEF (by rw [e]; intro h; cases h)) (hP c e)) hRT hOsR hRdF

/-- **rd12b's `kentry_rdyOff4r` with `InvRc C`.** -/
theorem kentry_rdyOffK {C : Fl4Invocation → Prop} (hA : ArmAK C) (hnd : numDomains = 1) (rep : Bool) (c : Syscall)
    (σ : State Unit) {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ InvRc C c w.2 ∧ RecvT rep c w.2 ∧ (RecvC c → A9.OsBody rep c w.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kentry_rdyOff4r hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    ⟨(hW w hw).1, invR_ofK hA (A8.ef_fip h w hw) (hW w hw).2.1, (hW w hw).2.2.1, (hW w hw).2.2.2⟩

end Q

end

end Fl4Proofs.P3.SInvR.A14d
