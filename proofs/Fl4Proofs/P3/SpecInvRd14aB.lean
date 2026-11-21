/-
P3 (DESIGN.md §9), invariant line G1 (rd14a, KENTRY-PLAN rd13a handoff 1-2):
**rd13a's `RecvTA` without its open disjunct; tops `kcall_rdyOff7` /
`kentry_rdyOff7`** (spec side only).

* `RcvR'` (rd13a's `RcvR` without `Simple`: Rdy, ScInv, ct not `BlkR`, rd8d's
  `RT ct`), `rcvW_of`; `RecvTB rep c σ`: `RcvR'` at every `ok` first-phase
  invocation outcome of the given entry — carried facts only, no frame and
  no `SS4` content.
* **`ss4_inv`**: `SS4` at such an outcome from rd12b's `InvR` (its shell
  `bq_shell` / `perfH_of`) and ctq's `CB` (inside `EB true`).
* **`recvT_of7`**: `InvR ∧ RecvTB ⇒` rd12b's `RecvT`, through
  SpecInvRd14aA's `ss4_handleRecvT` anchored at the outcome (covers ct
  unbound — passive-server ReplyRecv, NBSendRecv's donation — and cur_sc
  reconfigured: no frame back to the body start is needed).
* Tops **`kcall_rdyOff7` / `kentry_rdyOff7`**: rd13a's `*rdyOff6` with
  `RecvTA` replaced by `RecvTB`.
-/
import Fl4Proofs.P3.SpecInvRd14aA
open Classical

namespace Fl4Proofs.P3.SInvR.A14a
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.A11 Fl4Proofs.P3.SInvR.A12a
  Fl4Proofs.P3.SInvR.A13a

noncomputable section

set_option maxHeartbeats 1000000

/-- rd13a's `RcvR` without `Simple` (false after a send half that woke a
thread: possible_switch_to sets `switch_thread`). -/
def RcvR' (s : State Unit) : Prop :=
  Rdy s ∧ SInvB.ScInv s ∧ (∃ x, s.kheap s.curThread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) ∧
    B8d.RT s s.curThread

theorem rcvW_of {s : State Unit} (h : RcvR' s) (hE : SInvQ.EB true s) : RcvW s s.curThread :=
  ⟨h.1, h.2.1, (hE.2.1.2.1 rfl).2.1, (hE.2.1.2.1 rfl).1, (hE.2.1.2.1 rfl).2.2, h.2.2.1, h.2.2.2⟩

/-- **`RcvR'` at every `ok` first-phase invocation outcome** of the given
entry (pinned: the shell's actual run from every `true` front outcome).
Carried facts only, true in reachable states: `Rdy` (rd8h's invocation
carry, rd8j), `ScInv` (sb2), ct not blocked on receive / notification /
send (the first phase is non-blocking; a suspended ct is Inactive), `RT ct`
(ct unbound — passive server after the reply, donation —, or bound to
cur_sc whose head is ready: kept by rd11a's frame, or after configure of
cur_sc refilled at the current time by refill_new / refill_update after
commit_time). -/
def RecvTB (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ r cr, A12b.srArgs c = some (r, cr) →
    ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, t.1 = .ok () →
        RcvR' t.2

section P
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.P13
  Fl4Proofs.P3.SInvQ.P15 Fl4Proofs.P3.SInvQ.P17

/-- **rd12b's `RecvT` from `InvR` and `RecvTB`.** -/
theorem recvT_of7 (hnd : numDomains = 1) {rep : Bool} {c : Syscall} {σ : State Unit} {N S : ObjRef}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe : State Unit}
    (hEF : A8.EF σ) (hσ : EvP σ.curThread N S I d Nq σe σ) (hCN : σ.curThread ≠ N)
    (hP : A12b.InvR c σ) (hA : RecvTB rep c σ) : A12b.RecvT rep c σ := by
  unfold A12b.RecvT
  intro v hv ht r cr hc
  unfold A12b.RecvQ
  intro g hg t ht' hok y hy _
  obtain ⟨hB, hSf⟩ := A10.bs_front hEF hv ht
  have hz : A12b.KZ v.2 g.2 := A12b.kz_getCapReg (V := v.2) r v.2 rfl g hg
  have hg' : EvP σ.curThread N S I d Nq σe g.2 := evp_getCapReg r v.2 (evp_front hσ hv ht) g hg
  have hE1 : SInvQ.EB true t.2 :=
    (eb_fl4HandleInvocationR hnd σ.curThread N S rep false false true true g.1 (fun _ => rfl) hCN g.2
      hg'.1 t ht').2 () hok
  have hct : t.2.curThread = σ.curThread :=
    ct_fl4HandleInvocationR (cq := σ.curThread) rep false false true true g.1 g.2 hg'.1.1.2.1 t ht'
  have hN : NQ [t.2.curThread] t.2 := by
    rw [hct]
    exact (nq_fl4HandleInvocationR σ.curThread rep false false true true g.1 g.2 hg'.2.2.1 t ht').2 rfl
  have hid : t.2.idleThread = g.2.idleThread :=
    SInvG.idk_fl4HandleInvocationR (N := g.2.idleThread) rep false false true true g.1 g.2 rfl t ht'
  have hgc : g.2.curThread = σ.curThread := hg'.1.1.2.1
  have hni : t.2.curThread ≠ t.2.idleThread := by
    rw [hid, hct, ← hgc, A12b.kz_curThread hz, A12b.kz_idle hz]; exact hB.ni
  have hS4 : A10.SS4 t.2 :=
    (A12b.bq_shell hB hSf rep false false true true g.1 hz
      (A12b.perfH_of hB hSf hz ((hP v hv ht).2 r cr hc g hg)) t ht').1 () hok hE1.2.2
  have hR := hA v hv ht r cr hc g hg t ht' hok
  exact ss4_handleRecvT true cr t.2 hS4 (rcvW_of hR hE1) hE1 hN hni y hy

end P

/-! ## The tops -/

section Q
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

set_option maxHeartbeats 4000000 in
/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event** (rd14a top): rd13a's
`kcall_rdyOff6` with `RecvTA` (frame-or-open-tail) replaced by `RecvTB`
(carried facts at the first-phase invocation outcomes). Remaining named
hypotheses, pinned to the given entry's run: `hRdB` (rd8e/f/h, rd8j), `hP`
(`InvR`: the perform arms, rd14b), `hRA` (`RecvTB`), `hRdF` (rd8e/f, rd8j). -/
theorem kcall_rdyOff7 (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → A12b.InvR c σ)
    (hRA : ∀ c, ev = .syscallEvent c → RecvTB rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have key : ∀ c, ev = .syscallEvent c → A8.EF σ ∧
      EvP σ.curThread σ.idleThread σ.idleSc I d Nq σ σ ∧ σ.curThread ≠ σ.idleThread := by
    intro c e
    subst e
    obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS c rfl
    exact ⟨hEF (by intro h; cases h), evp_start hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ,
      ne_idle_of_active hX10.vi hCX (fun x hx => (ha x hx).resolve_right fun e => by cases e)⟩
  exact A12b.kcall_rdyOff4r hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB hP
    (fun c e => recvT_of7 hnd (key c e).1 (key c e).2.1 (key c e).2.2 (hP c e) (hRA c e))
    (fun c e hr => osBody_recv rep c hr (key c e).1 (rcvB_of (key c e).1 (key c e).2.1)) hRdF

set_option maxHeartbeats 4000000 in
/-- **The syscall entry** (rd14a top): rd13a's `kentry_rdyOff6` with `RecvTA`
replaced by `RecvTB`; `hW` keeps rd8e/f/h's `RdBody`, rd12b's `InvR` (rd14b)
and `RecvTB` at the FaultIP outcome. -/
theorem kentry_rdyOff7 (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ A12b.InvR c w.2 ∧ RecvTB rep c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A12b.kentry_rdyOff4r hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    have hF := fip_evp (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ w hw
    ⟨(hW w hw).1, (hW w hw).2.1,
      recvT_of7 hnd (A8.ef_fip h w hw) hF.1 hF.2 (hW w hw).2.1 (hW w hw).2.2,
      fun hr => osBody_recv rep c hr (A8.ef_fip h w hw) (rcvB_of (A8.ef_fip h w hw) hF.1)⟩

end Q

end

end Fl4Proofs.P3.SInvR.A14a
