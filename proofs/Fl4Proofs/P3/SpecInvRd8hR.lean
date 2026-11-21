/-
P3 (DESIGN.md §9), invariant line G1 (rd8h, lead item: handle_recv):
**`handle_recv` keeps `Rdy`; `RdBody` for the receive syscalls** (spec side
only, outside the JAtZ cone).

* `QC t s`: `t` in no ready queue and not in the release queue
  (`qc_setThreadState`, `qc_tcbNtfnAppend`; `simple_tcbNtfnAppend`).
* `tcb_tv`: rd8d's `TV` keeps a TCB's state and fault.
* `rd_receiveSignalBlocked` (the blocking arm: `set_thread_state` of an `RT`
  thread (rd8e's `rd_setThreadState_rt`), the queue append, RdU's
  `rd_maybeReturnSc_p` with `QC` / `Simple` carried) and
  **`rd_receiveSignal`** (the active arm: rd8e's `rd_completeSignal` shape —
  the badge write, the notification write, rd's `rd_maybeDonateSc_sr`, then
  the sporadic unblock check by `rd_ifCond`).
* `RH C s := RcvS s C ∧ RBk true s ∧ ct = C ∧ RdyT s C` (rd8e's receiver
  facts, ctq's `RB`, the current thread ready), carried by the register reads
  (`rh_asUser`), `lookup_reply` (`rh_lookupReply`) and the lookups (ctq's
  `pk_capFaultLookupCap`).
* **`rd_handleRecv C blk cr : HK (RH C) Rdy (handle_recv blk cr)`** (ctq's
  `eb_handleRecv_hr` skeleton): endpoint → rd8e's `rd_receiveIpc`,
  notification → `rd_receiveSignal`, lookup fault → Rd8hF's `rd_hf`.
* **`rdBody_recv`**: rd9's `RdBody rep c σ` for `Recv` / `Wait` / `NBWait` /
  `NBRecv` from rd8a's `EF`, ctq's `T1` and `RB`, and the action
  `resume_cur_thread` at the entry (ctq20's carried `RS`).
-/
import Fl4Proofs.P3.SpecInvRd8hF
import Fl4Proofs.P3.SpecInvRd8eB
import Fl4Proofs.P3.SpecInvRd10A2
import Fl4Proofs.P3.SpecInvCqB3
open Classical

namespace Fl4Proofs.P3.SInvR.B8h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8

noncomputable section

set_option maxHeartbeats 1000000

/-- `t` in no ready queue and not in the release queue. -/
abbrev QC (t : ObjRef) (s : State Unit) : Prop :=
  (∀ d p, t ∉ s.readyQueues d p) ∧ t ∉ s.releaseQueue

theorem qc_setThreadState (t u : ObjRef) (ts : ThreadState) : IK (QC t) (setThreadState (Z := Unit) u ts) := by
  unfold setThreadState
  repeat' (first | ik_step0 | ik_unfold)

theorem qc_tcbNtfnAppend (t u n : ObjRef) : IK (QC t) (tcbNtfnAppend (Z := Unit) u n) := by
  unfold tcbNtfnAppend
  repeat' (first | ik_step0 | ik_unfold)

theorem simple_tcbNtfnAppend (u n : ObjRef) : IK SInvQ.Simple (tcbNtfnAppend (Z := Unit) u n) := by
  unfold tcbNtfnAppend
  repeat' (first | ik_step0 | ik_unfold)

/-- rd8d's `TV` keeps a TCB's state and fault. -/
theorem tcb_tv {s s' : State Unit} {t : ObjRef} {x : Tcb} (hx : s.kheap t = some (.tcb x))
    (h : B8d.TV (B8d.TVv s) s') :
    ∃ x', s'.kheap t = some (.tcb x') ∧ x'.tcbState = x.tcbState ∧ x'.tcbFault = x.tcbFault := by
  have ev := congrFun h t
  unfold B8d.TVv at ev
  rw [hx] at ev
  cases hk : s'.kheap t with
  | none => rw [hk] at ev; simp [B8c.tcbV] at ev
  | some o =>
    rw [hk] at ev
    cases o with
    | tcb x3 =>
      simp only [B8c.tcbV, Option.some.injEq, Prod.mk.injEq] at ev
      exact ⟨x3, rfl, ev.1, ev.2.1⟩
    | _ => simp [B8c.tcbV] at ev

/-- **`receive_signal_blocked`** for an `RT` thread outside the queues. -/
theorem rd_receiveSignalBlocked (thread n : ObjRef) (blk : Bool) (s : State Unit) (hR : Rdy s)
    (hT : B8d.RT s thread) (hq : QC thread s) (hA : SInvQ.Simple s) :
    ∀ y ∈ (receiveSignalBlocked (Z := Unit) thread n blk s).1, Rdy y.2 := by
  intro y hy
  unfold receiveSignalBlocked at hy
  cases blk with
  | false => exact rd_doNbrecvFailedTransfer thread s hR y hy
  | true =>
    rw [if_pos (rfl : true = true)] at hy
    obtain ⟨z1, h1, hy⟩ := hy
    have e1 : Rdy z1.2 := B8e.rd_setThreadState_rt thread _ s hT hR z1 h1
    have q1 : QC thread z1.2 := qc_setThreadState thread thread _ s hq z1 h1
    have a1 : SInvQ.Simple z1.2 := B8d.simple_svs hA (SVK.sv_setThreadState' thread _ s z1 h1)
    obtain ⟨z2, h2, hy⟩ := hy
    have e2 : Rdy z2.2 := rd_tcbNtfnAppend thread n z1.2 e1 z2 h2
    have q2 : QC thread z2.2 := qc_tcbNtfnAppend thread thread n z1.2 q1 z2 h2
    have a2 : SInvQ.Simple z2.2 := simple_tcbNtfnAppend thread n z1.2 a1 z2 h2
    exact rd_maybeReturnSc_p n thread z2.2 q2.1 (a2 thread) q2.2 e2 y hy

/-- **`receive_signal`** of a non-`BlkR` thread, `RdyT` when bound, outside
the queues. -/
theorem rd_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (s : State Unit) (hR : Rdy s)
    {x : Tcb} (hx : s.kheap thread = some (.tcb x)) (hnb : ∀ f, ¬ BlkR x.tcbState f)
    (hT : B8d.RT s thread) (hq : QC thread s) (hA : SInvQ.Simple s) {y : Unit × State Unit}
    (hy : y ∈ (receiveSignal (Z := Unit) thread cap isBlocking s).1) : Rdy y.2 := by
  unfold receiveSignal at hy
  cases cap
  case notificationCap p b r =>
    dsimp only at hy
    obtain ⟨w0, hw0, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw0
    obtain ⟨⟨ntfn, s1⟩, hz1, hy⟩ := hy
    have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz1
    subst s1
    dsimp only at hy
    cases hn : ntfn.ntfnObj
    case activeNtfn badge =>
      rw [hn] at hy
      dsimp only at hy
      obtain ⟨z2, hz2, hy⟩ := hy
      have e2 : Rdy z2.2 := rd_asUser thread _ s hR z2 hz2
      have v2 : SVK.SVS s z2.2 := SVK.sv_asUser' thread _ s z2 hz2
      have t2 : B8d.TV (B8d.TVv s) z2.2 := B8d.tv_asUser thread _ s rfl z2 hz2
      obtain ⟨z3, hz3, hy⟩ := hy
      have e3 : Rdy z3.2 := rd_setSimpleKo _ _ _ z2.2 e2 z3 hz3
      have v3 : SVK.SVS z2.2 z3.2 :=
        SVK.sv_setSimpleKo' KernelObject.notification _ _ (SVK.so_ntfn _) z2.2 z3 hz3
      have t3 : B8d.TV (B8d.TVv s) z3.2 := B8e.tv_setNotification _ _ z2.2 t2 z3 hz3
      obtain ⟨x3, hx3, es, ef⟩ := tcb_tv hx t3
      have hT3 : B8d.RT z3.2 thread := B8d.rT_svs hT (v2.trans v3)
      obtain ⟨z4, hz4, hy⟩ := hy
      obtain ⟨e4, -⟩ := rd_maybeDonateSc_sr thread p z3.2 e3 hx3 (by rw [es]; exact hnb _)
        (fun c hc => hT3 x3 c hx3 hc) hz4
      obtain ⟨z5, hz5, hy⟩ := hy
      obtain ⟨x5, -, rfl⟩ := SInvQ.q1_mem_threadGet hz5
      exact (rd_ifCond x5.tcbSchedContext (some false) (some false) z4.2 e4 hy).1
    all_goals (rw [hn] at hy; dsimp only at hy; exact rd_receiveSignalBlocked thread p isBlocking s hR hT hq hA y hy)
  all_goals (dsimp only at hy; obtain ⟨w, hw, -⟩ := hy; exact hw.elim)

/-! ## `handle_recv` -/

/-- The receiver's facts at a state of `handle_recv`. -/
def RH (C : ObjRef) (s : State Unit) : Prop :=
  B8e.RcvS s C ∧ SInvQ.RBk true s ∧ s.curThread = C ∧ RdyT s C

theorem rh_asUser (C t : ObjRef) (r : Register) : IK (RH C) (asUser (Z := Unit) t (getRegister r)) := by
  intro s hs z hz
  obtain ⟨⟨hR, h1, hI, hA, hq, hrq, ⟨x, hx, hnb⟩, hT⟩, hB, hc, hRT⟩ := hs
  have v := SVK.sv_asUser' t _ s z hz
  have qc : (QC C z.2 ∧ z.2.curThread = C) :=
    (show IK (fun s : State Unit => QC C s ∧ s.curThread = C) (asUser (Z := Unit) t (getRegister r)) by
      unfold asUser; repeat' (first | ik_step0 | ik_unfold)) s ⟨⟨hq, hrq⟩, hc⟩ z hz
  obtain ⟨x', hx', hs', -⟩ := tcb_tv hx (B8d.tv_asUser t _ s rfl z hz)
  exact ⟨⟨rd_asUser t _ s hR z hz, q1_asUser t _ s h1 z hz,
    SInvB.sik_of_sbk (fun _ => SInvB.sb_asUser _ _) s hI z hz, B8d.simple_svs hA v, qc.1.1, qc.1.2,
    ⟨x', hx', by rw [hs']; exact hnb⟩, B8d.rT_svs hT v⟩, SInvQ.rb_asUser t _ s hB z hz, qc.2, rdyT_svs hRT v⟩

theorem rh_lookupReply (C : ObjRef) : IKE (RH C) (lookupReply (Z := Unit)) := by
  unfold lookupReply
  repeat' (first | (with_reducible exact rh_asUser _ _ _) |
    (with_reducible exact SInvQ.pk_capFaultLookupCap _ _ _ _) | ik_step0 | ik_unfold)

/-- **`handle_recv` keeps `Rdy`** from `RH C` (module docstring). -/
theorem rd_handleRecv (C : ObjRef) (blk canReply : Bool) :
    SInv.HK (RH C) Rdy (handleRecv (Z := Unit) blk canReply) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (RH C) m := fun h => SInvQ.ik_of_ro h
  have hRIP : ∀ cp rc, SInv.HK (RH C) Rdy (receiveIpc (Z := Unit) C cp blk rc) :=
    fun cp rc s hs y hy => B8e.rd_receiveIpc C cp blk rc s hs.1 hs.2.1 hs.2.2.1 hy
  have hRS : ∀ cp, SInv.HK (RH C) Rdy (receiveSignal (Z := Unit) C cp blk) := by
    intro cp s hs y hy
    obtain ⟨⟨hR, -, -, hA, hq, hrq, ⟨x, hx, hnb⟩, hT⟩, -, -, -⟩ := hs
    exact rd_receiveSignal C cp blk s hR hx hnb hT ⟨hq, hrq⟩ hA hy
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = C := hσ.2.2.1
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : RH C y2.2 := (?_ : IK (RH C) _) σ hσ y2 h2
  · refine hk_catch (I := RH C) (Q0 := Rdy) ?_ (fun e => ?_) y2.2 hb2 y hy
    · refine hkr_bind (SInvQ.pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (rh_lookupReply C) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
          · refine hkr_bind (ike_returnOk _) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
        · exact hkr_throw _
      · (try dsimp only)
        split
        · refine hkr_bind (hro fun _ => by repeat' (first | ik_step0 | ik_unfold)) (fun bt => ?_)
          split
          · exact hkr_liftE (hRS _)
          · exact hkr_throw _
        · exact hkr_throw _
      · exact hkr_throw _
    · intro s hs z hz
      obtain ⟨⟨hR, h1, hI, hA, -, -, -, -⟩, -, -, hRT⟩ := hs
      exact rd_hf C e s ⟨hR, hRT, h1, hA, hI⟩ z hz
  · repeat' (first | exact rh_asUser C _ _ | ik_step0)

/-- **rd9's `RdBody` for the receive syscalls** (`Recv`, `Wait`, `NBWait`,
`NBRecv`) from rd8a's `EF`, ctq's `T1` and `RB`, and `resume_cur_thread` at
the entry (ctq20's `RS`, carried at every exit). -/
theorem rdBody_recv (rep : Bool) (c : Syscall)
    (hc : c = .sysRecv ∨ c = .sysWait ∨ c = .sysNBWait ∨ c = .sysNBRecv) (σ : State Unit)
    (hEF : A8.EF σ) (h1 : T1 σ) (hRB : SInvQ.RBk true σ) (hRS : σ.schedulerAction = .resumeCurThread) :
    A9.RdBody rep c σ := by
  intro v hv ht y hy
  obtain ⟨xt, hct, hst⟩ := hEF.ct
  obtain ⟨-, -, h3⟩ := rd_front hEF.rdy hEF.off hEF.vmt hEF.sc hEF.cs hct hst hEF.q hEF.si hEF.cb hEF.hb
    hEF.ca hEF.ni hv
  obtain ⟨w, hw, e, -⟩ := h3 ht
  have hB := A10.bs_uts hEF hw
  obtain ⟨ek, -, -, -⟩ := SInvO.uts_off hw
  obtain ⟨eq, ea, er, -⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ w hw
  have h1w : T1 w.2 := by
    intro d p u hu; rw [eq] at hu; rw [ek]; exact h1 d p u hu
  have hRBw : SInvQ.RBk true w.2 := SInvQ.rb_updateTimeStamp σ hRB w hw
  have hH := hb_bs hB h1w
  obtain ⟨x, hx, hxs⟩ := hB.ct
  have hR : RH w.2.curThread w.2 := by
    refine ⟨⟨hB.rdy, h1w, hB.sc, hB.si, hB.q, hB.hb (by rw [ea]; exact hRS), ⟨x, hx, fun f hb => ?_⟩,
      B8d.rT_of_rdyT hH.2.1⟩, hRBw, rfl, hH.2.1⟩
    rcases hxs with h | h <;> rw [h] at hb <;>
      rcases hb with ⟨_, h'⟩ | ⟨_, _, h', -⟩ | ⟨_, _, _, h'⟩ <;> cases h'
  rw [e] at hy
  rcases hc with rfl | rfl | rfl | rfl
  · obtain ⟨z, hz, e'⟩ := A10.mem_handleE_wp (m := handleRecv (Z := Unit) true true) hy
    rw [e']; exact rd_handleRecv _ _ _ w.2 hR z hz
  · obtain ⟨z, hz, e'⟩ := A10.mem_handleE_wp (m := handleRecv (Z := Unit) true false) hy
    rw [e']; exact rd_handleRecv _ _ _ w.2 hR z hz
  · obtain ⟨z, hz, e'⟩ := A10.mem_handleE_wp (m := handleRecv (Z := Unit) false false) hy
    rw [e']; exact rd_handleRecv _ _ _ w.2 hR z hz
  · obtain ⟨z, hz, e'⟩ := A10.mem_handleE_wp (m := handleRecv (Z := Unit) false true) hy
    rw [e']; exact rd_handleRecv _ _ _ w.2 hR z hz

end

end Fl4Proofs.P3.SInvR.B8h
