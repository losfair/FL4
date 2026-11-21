/-
P3 (DESIGN.md §9), invariant line G1 (rd12b, KENTRY-PLAN rd11a goal 2):
**the finalise phase around the perform** (spec side only): SpecInvRd12bA's
`PerfH` reduced to a per-arm obligation on `fl4PerformInvocation` alone.

* `cb0_svcf` / `ke_svcf`: rd11a's `CB0` / `KE` across an `SVS ∧ cfS` step.
* `invPost` (the Restart check, the kernel reply and the Running write after
  the perform) and **`ke_post`**: `KE σ0` is kept (Restart is runnable, so
  rd11a's `KE` gives `CB0` on that branch; the writes are `SVS ∧ cfS`).
* **`kpc_restart`**: from `BS σ0` and `KZ σ0 s` (the decode's outcome),
  `set_thread_state ct Restart` ends in `KP σ0 ∧ CB0` (ct bound to cur_sc).
* **`PerfA σ0 bl call don oper s`** (the per-arm obligation: every `ok`
  outcome of the perform has `KE σ0`, every `error` (preemption) outcome has
  `CB → SS4` after the preemption path) and **`PerfR`** (`PerfA` at every
  Restart state reached by the shell's actual run: pinned, no ∀-states).
* **`perfH_of`**: `PerfR → PerfH` (from `BS σ0 ∧ Suff σ0`).
* **`perfA_svm`**: an arm whose perform is `SVM ∧ CFK` (lifted, no error)
  has `PerfA` from `KP σ0 ∧ CB0` at its start.
* `InvR` (`PerfR` at every `true` front outcome), `invP_of`; tops
  **`kcall_rdyOff4r` / `kentry_rdyOff4r`** (SpecInvRd12bB's tops with `InvR`
  in place of `InvP`).
-/
import Fl4Proofs.P3.SpecInvRd12bB
open Classical

namespace Fl4Proofs.P3.SInvR.A12b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `CB0` / `KE` across `SVS ∧ cfS` -/

theorem cb0_svcf {s s' : State Unit} (hb : A11.CB0 s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) :
    A11.CB0 s' := by
  have ec : s'.curSc = s.curSc := congrArg (fun p => p.2.1) hc
  have et : s'.curThread = s.curThread := congrArg (fun p => p.2.2.1) hc
  intro x hx
  rw [et] at hx
  have e := hS.1 s.curThread
  rw [hx] at e
  obtain ⟨y, hy, hys⟩ := SVK.sv_tcb (o := s.kheap s.curThread) (a := x.tcbSchedContext) e.symm
  rw [ec, ← hys]
  exact hb y hy

theorem ke_svcf {σ0 s s' : State Unit} (hK : A11.KP σ0 s) (hb : A11.CB0 s) (hS : SVK.SVS s s')
    (hc : cfS s' = cfS s) : A11.KP σ0 s' ∧ A11.CB0 s' :=
  ⟨A11.kp_step hK hc (A8.cw_of_svs hS) fun _ => ⟨hS.1 _, hS.1 _⟩, cb0_svcf hb hS hc⟩

/-! ## The post -/

/-- The Restart check, the kernel reply and the Running write after the perform. -/
def invPost (calling : Bool) (thread : ObjRef) (reply : List Data) : SMonad Unit Unit := do
  let state ← getThreadState thread
  match state with
  | .restart => do
    NonDet.when calling <|
      replyFromKernel thread (0, reply)
    setThreadState thread .running
  | _ => return ()

theorem sv_whenReply (calling : Bool) (t : ObjRef) (x : Data × List Data) :
    SVK.SVM (NonDet.when calling (replyFromKernel (Z := Unit) t x)) := by
  unfold NonDet.when; split
  · unfold replyFromKernel; sv_auto
  · sv_auto

theorem cfk_whenReply (calling : Bool) (t : ObjRef) (x : Data × List Data) :
    CFK (NonDet.when calling (replyFromKernel (Z := Unit) t x)) := by
  unfold NonDet.when; split
  · unfold replyFromKernel; cfk_auto
  · cfk_auto

/-- **The post keeps `KE σ0`.** -/
theorem ke_post (calling : Bool) (reply : List Data) {σ0 s : State Unit} (hK : A11.KE σ0 s) :
    ∀ y ∈ (invPost calling σ0.curThread reply s).1, A11.KE σ0 y.2 := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  dsimp only at hy
  revert hy
  generalize hst : x.tcbState = st
  cases st <;> intro hy
  case restart =>
    have hb : A11.CB0 s := by
      rcases hK.2 with h | h
      · exact h
      · rw [A11.kp_curThread hK.1] at h
        have := h x hx
        rw [hst] at this
        simp [runnable] at this
    obtain ⟨u, hu, hy⟩ := hy
    obtain ⟨k1, b1⟩ := ke_svcf hK.1 hb (sv_whenReply calling _ _ s u hu) (cfk_whenReply calling _ _ s u hu)
    obtain ⟨k2, b2⟩ := ke_svcf k1 b1 (SVK.sv_setThreadState' _ _ u.2 y hy) (cfk_setThreadState' _ _ u.2 y hy)
    exact ⟨k2, Or.inl b2⟩
  all_goals (rw [Set.mem_singleton_iff.1 hy]; exact hK)

/-! ## The Restart write -/

/-- **`set_thread_state ct Restart` from a `KZ σ0` state ends in `KP σ0 ∧ CB0`.** -/
theorem kpc_restart {σ0 s : State Unit} (hB : A10.BS σ0) (hz : KZ σ0 s) {u : Unit × State Unit}
    (hu : u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1) : A11.KP σ0 u.2 ∧ A11.CB0 u.2 := by
  have hb : A11.CB0 s := by
    intro x hx
    obtain ⟨x0, hx0, -, eb⟩ := kz_ct hz hx
    right; rw [← eb, kz_curSc hz]; exact hB.cs x0 hx0
  exact ke_svcf (kp_of_kz hz) hb (SVK.sv_setThreadState' _ _ s u hu) (cfk_setThreadState' _ _ s u hu)

/-! ## The per-arm obligation -/

/-- **The per-arm obligation**: from the Restart state `s`, every `ok`
outcome of the perform has `KE σ0` or (for arms that legitimately leave
rd11a's frame, e.g. a reschedule after rewriting cur_sc) `CB → SS4` after the
post, every `error` (preemption) outcome has `CB → SS4` after the preemption
path. -/
def PerfA (σ0 : State Unit) (blocking calling canDonate : Bool) (oper : Fl4Invocation) (s : State Unit) : Prop :=
  ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blocking calling canDonate oper).run s).1,
    (∀ a, y.1 = .ok a → A11.KE σ0 y.2 ∨
      ∀ q ∈ (invPost calling σ0.curThread a y.2).1, CB q.2 → A10.SS4 q.2) ∧
    (∀ e, y.1 = .error e → ∀ z ∈ (preemptionPath (Z := Unit) y.2).1, CB z.2 → A10.SS4 z.2)

/-- **`PerfA` pinned to the shell's run**: at every Restart state reached
through the lookups', the decode's and the Restart write's outcomes. -/
def PerfR (σ0 : State Unit) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) (σ : State Unit) :
    Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((invE firstPhase cptr σ.curThread w0.1 a).run s).1 →
    ∀ u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1, PerfA σ0 blocking calling canDonate b u.2

/-- **`PerfR` gives SpecInvRd12bA's `PerfH`.** -/
theorem perfH_of {σ0 σ : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (hz : KZ σ0 σ)
    {calling blocking don fp : Bool} {cptr : CapRef} (hR : PerfR σ0 calling blocking don fp cptr σ) :
    PerfH calling blocking don fp cptr σ := by
  intro w0 hw0 a s b s' ha hb y hy
  have et : σ.curThread = σ0.curThread := kz_curThread hz
  dsimp only [invFin] at hy
  obtain ⟨z, hz1, ⟨u0, -, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · unfold withoutPreemption at hz1; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz1; cases he
  unfold withoutPreemption at hz1
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz1
  have hP := hR w0 hw0 a s b s' ha hb w hw
  obtain ⟨z2, hz2, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · unfold withoutPreemption at hy
    obtain ⟨q, hq, rfl⟩ := ft_mem_liftE hy
    rw [et] at hq
    rcases (hP z2 hz2).1 r hr with hK | hQ
    · exact ⟨fun _ _ _ => A11.ss4_of_ke hB hS (ke_post calling r hK q hq), fun _ h => by cases h⟩
    · exact ⟨fun _ _ hc => hQ q hq hc, fun _ h => by cases h⟩
  · exact ⟨fun _ h => (by cases h), fun _ _ => (hP z2 hz2).2 e he⟩

/-- **An `SVM ∧ CFK` arm** (the perform is a lifted `SVM ∧ CFK` computation,
so it has no error outcome): `PerfA` from `KP σ0 ∧ CB0` at its start. -/
theorem perfA_svm {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation} {β : Type}
    {m : NonDet (State Unit) β} (hm : ∀ s, (fl4PerformInvocation (Z := Unit) bl call don oper).run s =
      (NonDetE.liftE (ε := Unit) (m >>= fun _ => pure [])).run s)
    (h1 : SVK.SVM m) (h2 : CFK m) (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don oper s := by
  intro y hy
  rw [hm] at hy
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hy
  obtain ⟨v, hv, hw⟩ := hw
  have hw' := Set.mem_singleton_iff.1 hw
  subst hw'
  obtain ⟨k, c⟩ := ke_svcf hK hb (h1 s v hv) (h2 s v hv)
  exact ⟨fun _ _ => Or.inl ⟨k, Or.inl c⟩, fun _ h => by cases h⟩

/-! ## The tops with `PerfR` -/

/-- **rd12b's open part, per arm**: `PerfR` at the shell's run from every
`true` front outcome (send syscalls and the send half). -/
def InvR (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true →
    (∀ r cl bl dn, sendArgs c = some (r, cl, bl, dn) →
      ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfR v.2 cl bl dn false g.1 g.2) ∧
    (∀ r cr, srArgs c = some (r, cr) → ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfR v.2 false false true true g.1 g.2)

theorem invP_of {c : Syscall} {σ : State Unit} (hEF : A8.EF σ) (h : InvR c σ) : InvP c σ := by
  intro v hv ht
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  exact ⟨fun r cl bl dn hc g hg =>
      perfH_of hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).1 r cl bl dn hc g hg),
    fun r cr hc g hg => perfH_of hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).2 r cr hc g hg)⟩

section Q
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

/-- **`kcall_rdyOff4` with the per-arm obligation `InvR`** (`PerfR`: the
perform alone, from the Restart state). -/
theorem kcall_rdyOff4r (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → InvR c σ)
    (hRT : ∀ c, ev = .syscallEvent c → RecvT rep c σ)
    (hOsR : ∀ c, ev = .syscallEvent c → RecvC c → A9.OsBody rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kcall_rdyOff4 hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB
    (fun c e => invP_of (hEF (by rw [e]; intro h; cases h)) (hP c e)) hRT hOsR hRdF

/-- **`kentry_rdyOff4` with `InvR`.** -/
theorem kentry_rdyOff4r (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ InvR c w.2 ∧ RecvT rep c w.2 ∧ (RecvC c → A9.OsBody rep c w.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kentry_rdyOff4 hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    ⟨(hW w hw).1, invP_of (A8.ef_fip h w hw) (hW w hw).2.1, (hW w hw).2.2.1, (hW w hw).2.2.2⟩

end Q

end

end Fl4Proofs.P3.SInvR.A12b
