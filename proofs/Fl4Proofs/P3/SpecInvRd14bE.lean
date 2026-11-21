/-
P3 (DESIGN.md §9), invariant line G1 (rd14b, lead's addition): **the combined
first-phase fact of ReplyRecv / NBSendRecv / NBSendWait** (spec side only).

At every `ok` outcome of the non-blocking, non-calling first phase
`fl4HandleInvocationR rep false false true true` the current thread is a TCB
that is not blocked (rd14a's `RecvTB` / rd15a's `RecvTC` / rd8m's `RcvIn`
conjunct `∃ x, ct tcb x ∧ ∀ f, ¬ BlkR`), `RT ct` (its SC, if any, is ready),
it is not IPC-queued and its SC, if any, is active (rd8l's `RP`:
`NotQ ct ∧ CBa ct`).

* `FPO s`: the combined fact; `fpo_of`, **`fpo_kz`** (at every `KZ σ0` state
  of the body from `A10.BS σ0`: ct Running, bound to cur_sc, cur_sc active
  with a ready head by `OffReady`).
* **`PerfF σ0 oper u`**: the per-arm obligation at the Restart state `u`:
  `FPO` after the post at every `ok` perform outcome. `PerfFR` pins it to the
  shell's run (as rd12b's `PerfR`), `InvF` to the entry (as rd12b's `InvR`).
* **`fpo_shell`**: from `BS σ0`, `KZ σ0 σ` and `PerfFR`, every `ok` outcome of
  the first phase has `FPO` (the lookup fault is not sent — blocking is false
  —, the error reply is skipped — calling is false —, both at `KZ σ0`
  states).
* `RecvF rep c σ` (the consumers' quantifier prefix, conclusion `FPO`),
  **`recvF_of (A8.EF σ) (InvF c σ) : RecvF rep c σ`**.
* **`perfF_svs`**: an arm whose `ok` outcomes are `SVS ∧ cfS`-related to the
  Restart state and leave ct Restart / Running / Inactive has `PerfF`, given
  `RT ct ∧ CBa ct` at the Restart state (`rtcba_restart`).
-/
import Fl4Proofs.P3.SpecInvRd14bD
import Fl4Proofs.P3.SpecInvRd8iA
import Fl4Proofs.P3.SpecInvRd8dA
open Classical

namespace Fl4Proofs.P3.SInvR.A14b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The combined fact -/

/-- **The combined first-phase fact** (module docstring). -/
def FPO (s : State Unit) : Prop :=
  ((∃ x, s.kheap s.curThread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) ∧ B8d.RT s s.curThread) ∧
    (B8i.NotQ s.curThread s ∧ B8i.CBa s.curThread s)

theorem nblk_of {ts : ThreadState} (h : ts = .running ∨ ts = .inactive ∨ ts = .idleThreadState)
    (f : Option Fault) : ¬ BlkR ts f := by
  rcases h with e | e | e <;> subst e <;> rintro (⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩) <;> cases h

theorem fpo_of {s : State Unit} {x : Tcb} (hx : s.kheap s.curThread = some (.tcb x))
    (hst : x.tcbState = .running ∨ x.tcbState = .inactive ∨ x.tcbState = .idleThreadState)
    (hR : B8d.RT s s.curThread) (hC : B8i.CBa s.curThread s) : FPO s := by
  refine ⟨⟨⟨x, hx, nblk_of hst⟩, hR⟩, fun x' hx' => ?_, hC⟩
  rw [hx] at hx'; cases hx'
  rcases hst with e | e | e <;> rw [e] <;> rfl

/-- **`FPO` at every `KZ σ0` state of the body.** -/
theorem fpo_kz {σ0 s : State Unit} (hB : A10.BS σ0) (hz : KZ σ0 s) : FPO s := by
  obtain ⟨xt, hxt, hst⟩ := hB.ct
  obtain ⟨xa, c, z, m, hxa, hca, hkz, hza⟩ := hB.ca hB.ni
  rw [hxt] at hxa; cases hxa
  rw [hB.cs xt hxt] at hca; cases hca
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have ecs : s.curSc = σ0.curSc := kz_curSc hz
  have hsc : s.kheap σ0.curSc = some (.schedContext z m) := by
    have e := (kz_parts hz).2.1 σ0.curSc
    rw [hkz] at e
    exact scO_some e
  have hO : Sched.OffReady s := A11.offReady_kp hB.off (kp_of_kz hz)
  obtain ⟨x, hx⟩ : ∃ x, s.kheap s.curThread = some (.tcb x) := by
    have e := (kz_parts hz).1 s.curThread
    rw [et, hxt] at e
    obtain ⟨x, hx, -⟩ := tcbV_some e
    exact ⟨x, by rw [et]; exact hx⟩
  obtain ⟨x0, hx0, est, esc⟩ := kz_ct hz hx
  rw [hxt] at hx0; cases hx0
  have hbx : x.tcbSchedContext = some σ0.curSc := by rw [← esc]; exact hB.cs xt hxt
  refine fpo_of hx ?_ ?_ ?_
  · rw [← est]; rcases hst with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr e)
  · intro x' c' hx' hc'
    rw [hx] at hx'; cases hx'
    exact ⟨x, σ0.curSc, z, m, hx, hbx, hsc, hza,
      ready_of_nat (Nat.le_trans (Nat.le_add_right _ _) (hO z m (by rw [ecs]; exact hsc)))⟩
  · intro x' c' hx' hc'
    rw [hx] at hx'; cases hx'
    rw [hbx] at hc'; cases hc'
    exact ⟨z, m, hsc, hza⟩

/-! ## The per-arm obligation -/

/-- **The per-arm obligation** at the Restart state `u` of the first phase:
`FPO` after the post at every `ok` outcome of the perform. -/
def PerfF (σ0 : State Unit) (oper : Fl4Invocation) (u : State Unit) : Prop :=
  ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false true oper).run u).1, ∀ a, y.1 = .ok a →
    ∀ q ∈ (invPost false σ0.curThread a y.2).1, FPO q.2

/-- **`PerfF` pinned to the first phase's run** (rd12b's `PerfR` shape). -/
def PerfFR (σ0 : State Unit) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((invE true cptr σ.curThread w0.1 a).run s).1 →
    ∀ u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1, PerfF σ0 b u.2

set_option maxHeartbeats 4000000 in
/-- **The first phase**: every `ok` outcome has `FPO`, given `PerfFR`. -/
theorem fpo_shell {σ0 : State Unit} (hB : A10.BS σ0) (rep : Bool) (cptr : CapRef) {σ : State Unit}
    (hz : KZ σ0 σ) (hP : PerfFR σ0 cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true cptr).run σ).1,
      ∀ u, y.1 = .ok u → FPO y.2 := by
  rw [fl4HandleInvocationR_eq]
  intro y hy
  obtain ⟨z, hz1, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz1; cases he
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz1
  obtain rfl := mem_gets hw
  simp only [Except.ok.injEq] at ha; subst ha
  obtain ⟨z, hz2, ⟨info, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · unfold withoutPreemption at hz2; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz2; cases he
  unfold withoutPreemption at hz2
  obtain ⟨w0, hw0, rfl⟩ := ft_mem_liftE hz2
  simp only [Except.ok.injEq] at ha; subst ha
  have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
  have et : σ.curThread = σ0.curThread := kz_curThread hz
  refine P17.syscall_r (I := KZ σ0) (Q := fun y => ∀ u, y.1 = .ok u → FPO y.2)
    (fun v hv => kz_invF _ _ _ w0.2 hz0 v hv) ?_ ?_ ?_ ?_ y hy
  · -- the fault branch: not sent (blocking is false)
    intro f s hs v hv _ _
    unfold NonDet.when at hv
    split at hv
    · rename_i h; cases h
    · rw [Set.mem_singleton_iff.1 hv]; exact fpo_kz hB hs
  · intro a s hs w hw
    exact kz_trans (kz_invF _ _ _ w0.2 hz0 _ hs) (kz_invE _ _ _ _ a s rfl w hw)
  · -- the error reply: skipped (calling is false)
    intro e s hs v hv _ _
    unfold NonDet.when at hv
    split at hv
    · rename_i h; cases h
    · rw [Set.mem_singleton_iff.1 hv]; exact fpo_kz hB hs
  · -- the Restart write, the perform, the post
    intro a s b s' ha hb _ y hy
    dsimp only [invFin] at hy
    obtain ⟨z, hz1, ⟨u0, -, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
    swap
    · unfold withoutPreemption at hz1; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz1; cases he
    unfold withoutPreemption at hz1
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz1
    have hF := hP w0 hw0 a s b s' ha hb w hw
    obtain ⟨z2, hz2, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
    · unfold withoutPreemption at hy
      obtain ⟨q, hq, rfl⟩ := ft_mem_liftE hy
      rw [et] at hq
      exact fun _ _ => hF z2 hz2 r hr q hq
    · intro _ h; cases h

/-! ## The entry -/

/-- **The combined fact at every first-phase outcome of the entry** (the
consumers' quantifier prefix: rd14a's `RecvTB`, rd15a's `RecvTC`, rd8m's
`RcvIn`; rd8l's `RP` reads the `NotQ ∧ CBa` half). -/
def RecvF (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ r cr, srArgs c = some (r, cr) →
    ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, t.1 = .ok () →
        FPO t.2

/-- **`PerfF` pinned to the entry** (rd12b's `InvR` shape, first phase only). -/
def InvF (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ r cr, srArgs c = some (r, cr) →
    ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfFR v.2 g.1 g.2

/-- **`RecvF` from the per-arm obligation.** -/
theorem recvF_of (rep : Bool) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ) (h : InvF c σ) : RecvF rep c σ := by
  intro v hv ht r cr hc g hg t htt hok
  obtain ⟨hB, -⟩ := A10.bs_front hEF hv ht
  exact fpo_shell hB rep g.1 (kz_getCapReg (V := v.2) r v.2 rfl g hg) (h v hv ht r cr hc g hg) t htt () hok

/-! ## Arms within the scheduler-view frame -/

/-- At the Restart state ct's SC, if any, is ready and active. -/
theorem rtcba_restart {σ0 s : State Unit} (hB : A10.BS σ0) (hz : KZ σ0 s) {u : Unit × State Unit}
    (hu : u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1) :
    B8d.RT u.2 σ0.curThread ∧ B8i.CBa σ0.curThread u.2 := by
  have hS := SVK.sv_setThreadState' _ _ s u hu
  have h := fpo_kz hB hz
  unfold FPO at h
  rw [kz_curThread hz] at h
  exact ⟨B8d.rT_svs h.1.2 hS, B8i.cba_sv h.2.2 hS⟩

/-- ct Restart (the post has not run), Running or Inactive. -/
abbrev QSt (t : ObjRef) (p : ObjRef) (x : Tcb) : Prop :=
  p = t → x.tcbState = .restart ∨ x.tcbState = .running ∨ x.tcbState = .inactive

/-- **An arm within the scheduler-view frame** that leaves ct Restart,
Running or Inactive has `PerfF`. -/
theorem perfF_svs {σ0 u : State Unit} {oper : Fl4Invocation}
    (hu : B8d.RT u σ0.curThread ∧ B8i.CBa σ0.curThread u) (et : u.curThread = σ0.curThread)
    (h : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false true oper).run u).1, ∀ a, y.1 = .ok a →
      SVK.SVS u y.2 ∧ cfS y.2 = cfS u ∧ TP (QSt σ0.curThread) y.2) : PerfF σ0 oper u := by
  intro y hy a ha q hq
  obtain ⟨hS, hc, hst⟩ := h y hy a ha
  have hR : B8d.RT y.2 σ0.curThread := B8d.rT_svs hu.1 hS
  have hC : B8i.CBa σ0.curThread y.2 := B8i.cba_sv hu.2 hS
  have ey : y.2.curThread = σ0.curThread := by rw [cf_curThread hc, et]
  obtain ⟨w, hw, hq⟩ := hq
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  dsimp only at hq
  rcases hst _ x hx rfl with e | e | e
  · rw [e] at hq
    obtain ⟨u1, hu1, hq⟩ := hq
    have hS1 := sv_whenReply false _ _ y.2 u1 hu1
    have hc1 := cfk_whenReply false _ _ y.2 u1 hu1
    have hS2 := SVK.sv_setThreadState' _ _ u1.2 q hq
    have hc2 := cfk_setThreadState' _ _ u1.2 q hq
    have eq : q.2.curThread = σ0.curThread := by rw [cf_curThread (hc2.trans hc1), ey]
    have e1 := (hS1.trans hS2).1 σ0.curThread
    rw [hx] at e1
    obtain ⟨x', hx0, -⟩ := SVK.sv_tcb (o := q.2.kheap σ0.curThread) (a := x.tcbSchedContext) e1
    have hx' : q.2.kheap q.2.curThread = some (.tcb x') := by rw [eq]; exact hx0
    refine fpo_of hx' (Or.inl (SInv.sts_post hq x' hx0)) ?_ ?_
    · rw [eq]; exact B8d.rT_svs hR (hS1.trans hS2)
    · rw [eq]; exact B8i.cba_sv hC (hS1.trans hS2)
  all_goals
    rw [e] at hq
    dsimp only at hq
    rw [Set.mem_singleton_iff.1 hq]
    show FPO y.2
    rw [← ey] at hx
    refine fpo_of hx ?_ (by rw [ey]; exact hR) (by rw [ey]; exact hC)
    rw [e]
    first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)

end

end Fl4Proofs.P3.SInvR.A14b
