/-
P3 (DESIGN.md §9), invariant line G1 (rd12b, KENTRY-PLAN rd11a goal 2):
**`OsBody` for the invocation syscalls: the shell** (spec side only).

* `kp_of_kz`: SpecInvRd12bF's `KZ σ0 s` (rd8c's `BKv`, `cfS` and the action
  of σ0) gives rd11a's pinned body frame `KP σ0 s`; `ss4_kz` (`SS4` at such a
  state from the body's start facts).
* The shell's exact pieces (`invF` the lookups, `invE` get_mrs + the decode,
  `invFin` the Restart write, the perform and its post) with
  `fl4HandleInvocationR_eq` (`rfl`).
* **`BodyQ y`**: an `ok` outcome has `CB → SS4`, an `error` (preemption)
  outcome has `CB → SS4` at every outcome of `preemption_path` (`CB` is
  ctq's, read at the body's outcome from ctq17's EBX).
* **`PerfH`**: `BodyQ` at every outcome of `invFin` reached by the shell's
  actual run (the lookups' and the decode's `ok` outcomes): the per-arm
  obligation, pinned to the run (no ∀-states).
* **`bq_shell`**: from `BS σ0 ∧ Suff σ0` and `KZ σ0 σ`, every outcome of
  `fl4HandleInvocationR` has `BodyQ`, given `PerfH` (fault branch: rd11b's
  `cp_handleFault` / `nr_handleFault` / `ss4_end`; error reply and the decode:
  the KZ family).
* **`osq_send`** (Send / NBSend / Call: every body outcome has `CB → SS4`)
  and **`osq_sendHalf`** (ReplyRecv / NBSendRecv / NBSendWait: the first
  phase, then rd12a's receive tail as a pinned hypothesis `RecvQ`).
-/
import Fl4Proofs.P3.SpecInvRd12bF
import Fl4Proofs.P3.SpecInvRd11A2
import Fl4Proofs.P3.SpecInvRd11bB
open Classical

namespace Fl4Proofs.P3.SInvR.A12b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `KZ` gives `KP` -/

/-- The SC part of an object (SpecInvEqV's `scAt` on one object). -/
def scO : Option KernelObject → Option (SchedContext × Nat)
  | some (.schedContext y n) => some (y, n)
  | _ => none

theorem scAt_eq (σ : State Unit) (p : ObjRef) : SInvE.scAt σ p = scO (σ.kheap p) := by
  unfold SInvE.scAt scO
  generalize σ.kheap p = o
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

/-- The scheduler view from the two views. -/
def svOf : Option (ThreadState × Option Fault × Option ObjRef) → Option (SchedContext × Nat) →
    Nat × Option ObjRef × List Refill × Nat × Option ObjRef × Nat
  | some (_, _, c), _ => (1, c, [], 0, none, 0)
  | none, some (y, n) => (2, none, y.scRefills, y.scRefillMax, y.scTcb, n)
  | none, none => (0, none, [], 0, none, 0)

theorem sv_eq_svOf (o : Option KernelObject) : SVK.sv o = svOf (B8c.tcbV o) (scO o) := by
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

theorem scO_some {o : Option KernelObject} {y : SchedContext} {n : Nat} (h : scO o = some (y, n)) :
    o = some (.schedContext y n) := by
  rcases o with _ | o
  · cases h
  · cases o <;> simp only [scO, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl

theorem tcbV_some {o : Option KernelObject} {v : ThreadState × Option Fault × Option ObjRef}
    (h : B8c.tcbV o = some v) : ∃ x, o = some (.tcb x) ∧ (x.tcbState, x.tcbFault, x.tcbSchedContext) = v := by
  rcases o with _ | o
  · cases h
  · cases o <;> simp only [B8c.tcbV, Option.some.injEq, reduceCtorEq] at h
    exact ⟨_, rfl, h⟩

/-- The pieces of `KZ`. -/
theorem kz_parts {σ0 s : State Unit} (h : KZ σ0 s) :
    (∀ p, B8c.tcbV (s.kheap p) = B8c.tcbV (σ0.kheap p)) ∧ (∀ p, scO (s.kheap p) = scO (σ0.kheap p)) ∧
      cfS s = cfS σ0 ∧ s.schedulerAction = σ0.schedulerAction := by
  unfold KZ KZv B8c.BKv CAv at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2, -⟩, h3, h4⟩ := h
  refine ⟨fun p => congrFun h1 p, fun p => ?_, h3, h4⟩
  rw [← scAt_eq, ← scAt_eq, h2]

theorem kz_sv {σ0 s : State Unit} (h : KZ σ0 s) (p : ObjRef) : SVK.sv (s.kheap p) = SVK.sv (σ0.kheap p) := by
  obtain ⟨h1, h2, -, -⟩ := kz_parts h
  rw [sv_eq_svOf, sv_eq_svOf, h1, h2]

theorem kz_trans {σ0 s s' : State Unit} (h : KZ σ0 s) (h' : KZ s s') : KZ σ0 s' := by
  unfold KZ at *; rw [h', h]

/-- **`KZ` gives rd11a's pinned body frame.** -/
theorem kp_of_kz {σ0 s : State Unit} (h : KZ σ0 s) : A11.KP σ0 s := by
  obtain ⟨-, h2, h3, h4⟩ := kz_parts h
  refine ⟨h3, ⟨fun y n hy => ?_, fun e => by rw [← h4]; exact e⟩, fun _ => ⟨kz_sv h _, kz_sv h _⟩⟩
  have e := h2 σ0.curSc
  rw [hy] at e
  exact ⟨y, n, scO_some e.symm, rfl, rfl⟩

theorem kz_curThread {σ0 s : State Unit} (h : KZ σ0 s) : s.curThread = σ0.curThread :=
  A11.kp_curThread (kp_of_kz h)

theorem kz_curSc {σ0 s : State Unit} (h : KZ σ0 s) : s.curSc = σ0.curSc := A11.kp_curSc (kp_of_kz h)

theorem kz_idle {σ0 s : State Unit} (h : KZ σ0 s) : s.idleThread = σ0.idleThread :=
  congrArg (fun p => p.2.2.2.1) (kz_parts h).2.2.1

/-- ct's TCB under `KZ`: same state and SC. -/
theorem kz_ct {σ0 s : State Unit} (h : KZ σ0 s) {x : Tcb} (hx : s.kheap s.curThread = some (.tcb x)) :
    ∃ x0, σ0.kheap σ0.curThread = some (.tcb x0) ∧ x0.tcbState = x.tcbState ∧
      x0.tcbSchedContext = x.tcbSchedContext := by
  have e := (kz_parts h).1 s.curThread
  rw [hx, kz_curThread h] at e
  obtain ⟨x0, hx0, ev⟩ := tcbV_some e.symm
  simp only [Prod.mk.injEq] at ev
  exact ⟨x0, hx0, ev.1, ev.2.2⟩

/-- **`SS4` at a `KZ` state** of the body. -/
theorem ss4_kz {σ0 s : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (h : KZ σ0 s) : A10.SS4 s := by
  refine A11.ss4_of_kp hB hS (kp_of_kz h) (A11.ctR_kp hB (kp_of_kz h) fun x hx => Or.inr ?_)
  obtain ⟨x0, hx0, -, eb⟩ := kz_ct h hx
  rw [← eb, kz_curSc h]; exact hB.cs x0 hx0

/-- ct is not receive-blocked at a `KZ` state (rd11b's `nb0_of_bs`). -/
theorem nb0_kz {σ0 s : State Unit} (hB : A10.BS σ0) (h : KZ σ0 s) : TP (A11b.NB0 s.curThread) s := by
  obtain ⟨xt, hct, hst⟩ := hB.ct
  intro p x hp ep e r d hx
  subst ep
  obtain ⟨x0, hx0, es, -⟩ := kz_ct h hp
  rw [hct] at hx0; cases hx0
  rw [← es] at hx
  rcases hst with hs | hs <;> rw [hs] at hx <;> cases hx

/-! ## The shell's pieces -/

/-- The lookups (the `syscall` fault phase of `fl4HandleInvocationR`). -/
def invF (thread : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    FMonad Unit (CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) := do
  let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot thread cptr
  let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
  let extracaps ← lookupExtraCaps thread buffer info
  NonDetE.returnOk (slot, cap, extracaps, buffer)

/-- `get_mrs` and the decode (the error phase). -/
def invE (firstPhase : Bool) (cptr : CapRef) (thread : ObjRef) (info : MessageInfo) :
    CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef → SEMonad Unit Fl4Invocation :=
  fun (slot, cap, extracaps, buffer) => do
    let args ← NonDetE.liftE <| getMrs thread buffer info
    fl4DecodeInvocation firstPhase info.miLabel args cptr slot cap extracaps buffer

/-- The Restart write, the perform and its post (the finalise phase). -/
def invFin (calling blocking canDonate : Bool) (thread : ObjRef) : Fl4Invocation → PMonad Unit Unit :=
  fun oper => do
    withoutPreemption <| setThreadState thread .restart
    let reply ← fl4PerformInvocation blocking calling canDonate oper
    withoutPreemption <| do
        let state ← getThreadState thread
        match state with
        | .restart => do
          NonDet.when calling <|
            replyFromKernel thread (0, reply)
          setThreadState thread .running
        | _ => return ()

theorem fl4HandleInvocationR_eq (rep calling blocking canDonate firstPhase : Bool) (cptr : CapRef) :
    fl4HandleInvocationR (Z := Unit) rep calling blocking canDonate firstPhase cptr = (do
      let thread ← NonDetE.liftE <| NonDet.gets fun s : State Unit => s.curThread
      let info ← withoutPreemption <| getMessageInfo thread
      syscall (invF thread cptr info) (fun fault => NonDet.when blocking <| handleFault thread fault)
        (invE firstPhase cptr thread info)
        (fun err => NonDet.when calling <| fl4ReplyFromKernelError rep thread <| msgFromSyscallError err)
        (invFin calling blocking canDonate thread)) := rfl

/-! ## The per-outcome post and the per-arm obligation -/

/-- **The body's post** (`CB` read at the body's outcome from ctq17's EBX). -/
abbrev BodyQ {α : Type} (y : Except Unit α × State Unit) : Prop :=
  (∀ a, y.1 = .ok a → CB y.2 → A10.SS4 y.2) ∧
    (∀ e, y.1 = .error e → ∀ z ∈ (preemptionPath (Z := Unit) y.2).1, CB z.2 → A10.SS4 z.2)

/-- **The per-arm obligation, pinned to the shell's run from σ**: `BodyQ` at
every outcome of the finalise phase reached through the lookups' and the
decode's `ok` outcomes. -/
def PerfH (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((invE firstPhase cptr σ.curThread w0.1 a).run s).1 →
    ∀ y ∈ ((invFin calling blocking canDonate σ.curThread b).run s').1, BodyQ y

/-! ## KZ across the front -/

theorem kz_fl4ReplyFromKernelError (rep : Bool) (t : ObjRef) (x : Data × List Data) :
    KZK V (fl4ReplyFromKernelError (Z := Unit) rep t x) := by
  unfold fl4ReplyFromKernelError; kz_auto

theorem kz_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : KZKE V (invF t cptr info) := by
  unfold invF; kz_auto

theorem kz_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : KZKE V (invE fp cptr t info a) := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold invE; kz_auto

/-! ## The shell -/

set_option maxHeartbeats 4000000 in
/-- **The invocation shell**: from the body's start facts and `KZ σ0 σ`, every
outcome of `fl4HandleInvocationR` has `BodyQ`, given the pinned per-arm
obligation `PerfH`. -/
theorem bq_shell {σ0 : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (rep calling blocking don fp : Bool)
    (cptr : CapRef) {σ : State Unit} (hz : KZ σ0 σ) (hP : PerfH calling blocking don fp cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr).run σ).1, BodyQ y := by
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
  refine P17.syscall_r (I := KZ σ0) (Q := BodyQ) (fun v hv => kz_invF _ _ _ w0.2 hz0 v hv) ?_ ?_ ?_
    (fun a s b s' ha hb _ y hy => hP w0 hw0 a s b s' ha hb y hy) y hy
  · -- the fault branch
    intro f s hs v hv
    refine ⟨fun _ _ hCB => ?_, fun _ e => by cases e⟩
    have ec : σ.curThread = s.curThread := by rw [kz_curThread hs, kz_curThread hz]
    unfold NonDet.when at hv
    split at hv
    · rw [ec] at hv
      have hP1 := A11b.cp_handleFault s.curThread f s s.curSc s ⟨rfl, A8.CW.refl _ _⟩ v hv
      have hc := A11b.cfk_handleFault s.curThread f s v hv
      have hN := A11b.nr_handleFault s.curThread f s (nb0_kz hB hs) v hv
      have hni : s.curThread ≠ s.idleThread := by rw [kz_curThread hs, kz_idle hs]; exact hB.ni
      exact A11b.ss4_end (ss4_kz hB hS hs).1 hP1 hc hN hCB hni
    · rw [Set.mem_singleton_iff.1 hv]; exact ss4_kz hB hS hs
  · -- the decode
    intro a s hs w hw
    exact kz_trans (kz_invF _ _ _ w0.2 hz0 _ hs) (kz_invE _ _ _ _ a s rfl w hw)
  · -- the error reply
    intro e s hs v hv
    refine ⟨fun _ _ _ => ?_, fun _ e => by cases e⟩
    have h1 : KZ s v.2 := (show KZK s (NonDet.when calling <|
      fl4ReplyFromKernelError (Z := Unit) rep σ.curThread (msgFromSyscallError e)) by
        unfold NonDet.when; split
        · exact kz_fl4ReplyFromKernelError _ _ _
        · exact ik_pure _) s rfl v hv
    exact ss4_kz hB hS (kz_trans hs h1)

/-! ## The body -/

theorem mem_handleE_cases {α : Type} {m : NonDetE (State Unit) Unit α} {h : Unit → NonDetE (State Unit) Unit α}
    {s : State Unit} {y : Except Unit α × State Unit} (hy : y ∈ (ExceptT.run (NonDetE.handleE m h) s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ y = (.ok a, z.2)) ∨ (∃ e, z.1 = .error e ∧ y ∈ ((h e).run z.2).1) := by
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact ⟨_, hz, Or.inl ⟨a, rfl, Set.mem_singleton_iff.1 hy⟩⟩
  | error e => exact ⟨_, hz, Or.inr ⟨e, rfl, hy⟩⟩

/-- The body outcomes from `BodyQ` at the outcomes of the handled computation. -/
theorem body_of_bq {m : PMonad Unit Unit} {s : State Unit} (h : ∀ z ∈ (m.run s).1, BodyQ z) :
    ∀ y ∈ (ExceptT.run (NonDetE.handleE m fun _ => withoutPreemption (Z := Unit) preemptionPath) s).1,
      CB y.2 → A10.SS4 y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a, ha, rfl⟩ | ⟨e, he, hy⟩⟩ := mem_handleE_cases hy
  · exact (h z hz).1 a ha
  · unfold withoutPreemption at hy
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hy
    exact (h z hz).2 e he w hw

/-- The register and flags of a send syscall. -/
def sendArgs : Syscall → Option (Register × Bool × Bool × Bool)
  | .sysSend => some (cap_register, false, true, false)
  | .sysNBSend => some (cap_register, false, false, false)
  | .sysCall => some (cap_register, true, true, true)
  | _ => none

/-- **Send / NBSend / Call**: every body outcome has `CB → SS4`, given the
pinned per-arm obligation at the shell's start. -/
theorem osq_send {σ0 : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (rep : Bool) (c : Syscall)
    {r : Register} {calling blocking don : Bool} (hc : sendArgs c = some (r, calling, blocking, don))
    (hP : ∀ g ∈ (getCapReg (Z := Unit) r σ0).1, PerfH calling blocking don false g.1 g.2) :
    ∀ y ∈ (A8.bodyRun rep c σ0).1, CB y.2 → A10.SS4 y.2 := by
  refine body_of_bq fun z hz => ?_
  have hsh : ∀ g ∈ (getCapReg (Z := Unit) r σ0).1,
      ∀ z ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don false g.1).run g.2).1, BodyQ z :=
    fun g hg => bq_shell hB hS rep calling blocking don false g.1 (kz_getCapReg (V := σ0) r σ0 rfl g hg) (hP g hg)
  cases c <;> simp only [sendArgs, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hc <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc <;> simp only [fl4HandleSyscall] at hz <;>
    · obtain ⟨u, hu, ⟨a, ha, hz⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hz
      swap
      · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hu; cases he
      obtain ⟨g, hg, rfl⟩ := ft_mem_liftE hu
      simp only [Except.ok.injEq] at ha; subst ha
      exact hsh g hg z hz

/-- The register and receive flag of a send-receive syscall. -/
def srArgs : Syscall → Option (Register × Bool)
  | .sysReplyRecv => some (replyRegister, true)
  | .sysNBSendRecv => some (nbsendRecvDest, true)
  | .sysNBSendWait => some (replyRegister, false)
  | _ => none

/-- **rd12a's receive tail, pinned**: after an `ok` first phase reached from
σ0, every outcome of `handle_recv` has `CB → SS4`. -/
def RecvQ (rep : Bool) (r : Register) (canReply : Bool) (σ0 : State Unit) : Prop :=
  ∀ g ∈ (getCapReg (Z := Unit) r σ0).1,
    ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, t.1 = .ok () →
      ∀ y ∈ (handleRecv (Z := Unit) true canReply t.2).1, CB y.2 → A10.SS4 y.2

/-- **ReplyRecv / NBSendRecv / NBSendWait**: the send half (`bq_shell` with the
first phase), then the receive tail `RecvQ`. -/
theorem osq_sendHalf {σ0 : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (rep : Bool) (c : Syscall)
    {r : Register} {cr : Bool} (hc : srArgs c = some (r, cr))
    (hP : ∀ g ∈ (getCapReg (Z := Unit) r σ0).1, PerfH false false true true g.1 g.2)
    (hR : RecvQ rep r cr σ0) :
    ∀ y ∈ (A8.bodyRun rep c σ0).1, CB y.2 → A10.SS4 y.2 := by
  refine body_of_bq fun z hz => ?_
  have key : ∀ g ∈ (getCapReg (Z := Unit) r σ0).1,
      ∀ z ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1 >>= fun _ =>
        withoutPreemption (Z := Unit) (handleRecv true cr)).run g.2).1, BodyQ z := by
    intro g hg z hz
    obtain ⟨t, ht, ⟨a, ha, hz⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hz
    · unfold withoutPreemption at hz
      obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      have ht' : t.1 = .ok () := by rw [ha]
      exact ⟨fun _ _ hCB => hR g hg t ht ht' w hw hCB, fun _ e => by cases e⟩
    · have hq := bq_shell hB hS rep false false true true g.1 (kz_getCapReg (V := σ0) r σ0 rfl g hg) (hP g hg) t ht
      refine ⟨fun _ e => (by cases e), fun _ _ => ?_⟩
      exact hq.2 e he
  cases c <;> simp only [srArgs, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hc <;>
    obtain ⟨rfl, rfl⟩ := hc <;> simp only [fl4HandleSyscall] at hz <;>
    · obtain ⟨u, hu, ⟨a, ha, hz⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hz
      swap
      · unfold withoutPreemption at hu; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hu; cases he
      unfold withoutPreemption at hu
      obtain ⟨g, hg, rfl⟩ := ft_mem_liftE hu
      simp only [Except.ok.injEq] at ha; subst ha
      exact key g hg z hz

end

end Fl4Proofs.P3.SInvR.A12b
