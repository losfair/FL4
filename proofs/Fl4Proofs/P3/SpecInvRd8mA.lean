/-
P3 (DESIGN.md §9), invariant line G1 (rd8m, KENTRY-PLAN rd8j handoff 1(a)):
**`handle_fault` and `handle_recv` for a faulting / receiving thread that may
be unbound** (spec side only, outside the JAtZ cone).

After the reply phase of ReplyRecv / NBSendRecv / NBSendWait a passive
server's ct may be unbound (reply_remove returns the donated SC), so rd8h's
`rd_hf` (which asks `RdyT t`) does not apply to `handle_recv`'s lookup-fault
branch there. Here every `RdyT t` of that path is replaced by rd8d's `RT t`
(`RdyT` if bound):

* `rd_threadSet_rt` (a TCB write keeping the SC and `SV`, `t` `RT`),
  `fh_factsT` (rd8h's `fh_facts` with `RT`).
* `rd_sendArm_dT` / **`rd_sendIpc_dT`**: rd8d's send with an `RT` sender, and
  `RdyT` only when `canDonate` (the donation reads the sender's SC).
  `handle_fault` passes `canDonate = (sender bound)`, so `RT` gives it.
* `HBT t := Rdy ∧ RT t ∧ T1 ∧ Simple ∧ ScInv`, `rd_sendFaultIpcT`,
  **`rd_hfT`**.
* `RHT C := RcvS C ∧ RBk true ∧ ct = C` (rd8h's `RH` without `RdyT C`),
  **`rd_handleRecvT`**.
-/
import Fl4Proofs.P3.SpecInvRd8hR
open Classical

namespace Fl4Proofs.P3.SInvR.B8m

noncomputable section

set_option maxHeartbeats 1000000

section D
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d

/-- A TCB write keeping the SC and the scheduler view at an `RT` thread. -/
theorem rd_threadSet_rt (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit)
    (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext)
    (hSV : ∀ x, SV (some (.tcb (f x))) = SV (some (.tcb x))) (hT : B8d.RT σ t) :
    IKp Rdy σ (threadSet (Z := Unit) f t) := by
  intro hR r hr
  by_cases hb : ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c
  · obtain ⟨x, c, hx, hc⟩ := hb
    exact rd_threadSet_r f t σ hf (hT x c hx hc) hR r hr
  · obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hr
    have hn : x.tcbSchedContext = none := by
      cases h : x.tcbSchedContext with
      | none => rfl
      | some c => exact absurd ⟨x, c, hx, h⟩ hb
    rw [e]
    refine rdy_upd hR t _ ⟨fun x0 h => ?_, fun x' h _ hc => ?_, by rw [hx]; exact hSV x⟩
    · rw [hx] at h; cases h; exact ⟨_, rfl, hf x⟩
    · cases h; exact absurd ((hf x).trans hn) hc

/-- rd8h's `fh_facts` with `RT t`. -/
theorem fh_factsT {s s' : State Unit} {t : ObjRef} {x x' : Tcb} (hx : s.kheap t = some (.tcb x))
    (hk' : s'.kheap = Function.update s.kheap t (some (.tcb x'))) (hq : s'.readyQueues = s.readyQueues)
    (htm : s'.curTime = s.curTime)
    (hsc : x'.tcbSchedContext = x.tcbSchedContext) (hd : x'.tcbDomain = x.tcbDomain)
    (hp : x'.tcbPriority = x.tcbPriority) (hT : B8d.RT s t) (h1 : SInvQ.T1 s) (hF : SInvB.ScFwd s) :
    B8d.RT s' t ∧ SInvQ.T1 s' ∧ SInvB.ScFwd s' := by
  have hk : ∀ q, q ≠ t → s'.kheap q = s.kheap q := fun q hq => by rw [hk']; exact Function.update_of_ne hq _ _
  have ht : s'.kheap t = some (.tcb x') := by rw [hk']; exact Function.update_self _ _ _
  refine ⟨?_, ?_, ?_⟩
  · intro x'' c hx'' hc
    rw [ht] at hx''; cases hx''
    exact (B8h.fh_facts hx hk' hq htm hsc hd hp (hT x c hx (hsc.symm.trans hc)) h1 hF).1
  · intro d p u hu
    rw [hq] at hu
    obtain ⟨x0, hx0, h1d, h1p⟩ := h1 d p u hu
    by_cases e : u = t
    · subst e; rw [hx] at hx0; cases hx0; exact ⟨x', ht, hd.trans h1d, hp.trans h1p⟩
    · exact ⟨x0, by rw [hk u e]; exact hx0, h1d, h1p⟩
  · intro p y n u hy hu
    have hpt : p ≠ t := by rintro rfl; rw [ht] at hy; cases hy
    rw [hk p hpt] at hy
    obtain ⟨x0, hx0, hs0⟩ := hF p y n u hy hu
    by_cases e : u = t
    · subst e; rw [hx] at hx0; cases hx0; exact ⟨x', ht, hsc.trans hs0⟩
    · exact ⟨x0, by rw [hk u e]; exact hx0, hs0⟩

/-- **rd8d's transfer to a waiting receiver with an `RT` sender** (`RdyT` only
when `canDonate`). -/
theorem rd_sendArm_dT (call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr dest : ObjRef)
    (reply : Option ObjRef) (s : State Unit) (hs : Rdy s) (h1 : SInvQ.T1 s) (hA : SInvQ.Simple s)
    (hF : SInvB.ScFwd s) (hct : B8d.RT s thread) (hcd : cd = true → RdyT s thread) (hRT : B8d.RT s dest)
    (y : Unit × State Unit)
    (hy : y ∈ ((do
      doIpcTransfer (Z := Unit) thread (some epptr) badge cg dest
      NonDet.maybeM (replyUnlinkTcb (Z := Unit) dest) reply
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      let fault ← threadGet (Z := Unit) Tcb.tcbFault thread
      if call ∨ fault ≠ none then
        if (cg ∨ cgr) ∧ reply ≠ none then
          replyPush (Z := Unit) thread dest (the reply) cd
        else
          setThreadState (Z := Unit) thread .inactive
      else NonDet.when (cd ∧ scOpt = none) <| do
        let threadSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext thread
        schedContextDonate (Z := Unit) (the threadSc) dest
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) destSc
      possibleSwitchTo (Z := Unit) dest) s).1) : Rdy y.2 := by
  obtain ⟨z3, h3, hy⟩ := hy
  have e3 : Rdy z3.2 := rd_doIpcTransfer thread (some epptr) badge cg dest s hs z3 h3
  have v3 : SVK.SVS s z3.2 := SVK.sv_doIpcTransfer' thread (some epptr) badge cg dest s z3 h3
  have q3 : SInvQ.T1 z3.2 := SInvQ.q1_doIpcTransfer thread (some epptr) badge cg dest s h1 z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  have e4 : Rdy z4.2 := (ik_maybeM (fun r => rd_replyUnlinkTcb dest r) reply) z3.2 e3 z4 h4
  have v4 : SVK.SVS s z4.2 :=
    v3.trans (SVK.sv_maybeM (fun r => SVK.sv_replyUnlinkTcb dest r) reply z3.2 z4 h4)
  have q4 : SInvQ.T1 z4.2 := (ik_maybeM (fun r => SInvQ.q1_replyUnlinkTcb dest r) reply) z3.2 q3 z4 h4
  have hA4 := simple_svs hA v4
  have hF4 := fwd_svs hF v4
  have hc4 := B8d.rT_svs hct v4
  have hd4 : cd = true → RdyT z4.2 thread := fun h => rdyT_svs (hcd h) v4
  have hT4 := B8d.rT_svs hRT v4
  obtain ⟨z5, h5, hy⟩ := hy
  obtain ⟨x5, hx5, rfl⟩ := SInvQ.q1_mem_threadGet h5
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  dsimp only at hy
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨e7, t7⟩ := rd_replyPush_d thread dest _ cd z4.2 e4 q4 hA4 hF4 (fun _ => hc4) h7
      exact rd_sendTail dest z7.2 e7 (t7 hT4) y hy
    · obtain ⟨z7, h7, hy⟩ := hy
      exact rd_sendTail dest z7.2 (rd_setThreadState thread .inactive trivial z4.2 e4 z7 h7)
        (B8d.rT_svs hT4 (SVK.sv_setThreadState' thread .inactive z4.2 z7 h7)) y hy
  · obtain ⟨z7, h7, hy⟩ := hy
    unfold NonDet.when at h7
    split at h7
    · rename_i hg
      obtain ⟨z8, h8, h7⟩ := h7
      obtain ⟨x8, hx8, rfl⟩ := SInvQ.q1_mem_threadGet h8
      have hc4' := hd4 hg.1
      obtain ⟨xt, c, yc, nc, hxt, hcc, -, -, -⟩ := id hc4'
      rw [hxt] at hx8
      cases hx8
      dsimp only at h7
      rw [hcc] at h7
      obtain ⟨r1, r2⟩ := rd_schedContextDonate_relT c dest z4.2 e4 q4 hA4 hF4 hx5 hg.2
        (rel_of_rdyT hc4' hxt hcc) h7
      exact rd_sendTail dest z7.2 r1 (B8d.rT_of_rdyT r2) y hy
    · obtain rfl := Set.mem_singleton_iff.1 h7
      exact rd_sendTail dest z4.2 e4 hT4 y hy

/-- **`send_ipc` from an `RT` sender**, `RdyT` only when `canDonate`. -/
theorem rd_sendIpc_dT (block call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr : ObjRef)
    (σ : State Unit) (hct : B8d.RT σ thread) (hcd : cd = true → RdyT σ thread) (h1 : SInvQ.T1 σ)
    (hA : SInvQ.Simple σ) (hF : SInvB.ScFwd σ) :
    IKp Rdy σ (sendIpc (Z := Unit) block call badge cg cgr cd thread epptr) := by
  unfold sendIpc
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨hk, ez⟩ := SInvI.mem_getSimpleKo hz
  obtain ⟨ep, z2⟩ := z
  simp only at hk ez; subst z2
  revert hy
  refine (show IKp Rdy σ _ from ?_) hσ y
  cases ep with
  | idleEP =>
    cases block
    · exact ikp_of_ik (ik_pure _) σ
    · unfold sendIpcBlocked
      exact ikp_bind (B8e.rd_setThreadState_rt thread _ σ hct) fun _ => rd_tcbEpAppend _ _ _
  | sendEP q =>
    cases block
    · exact ikp_of_ik (ik_pure _) σ
    · unfold sendIpcBlocked
      exact ikp_bind (B8e.rd_setThreadState_rt thread _ σ hct) fun _ => rd_tcbEpAppend _ _ _
  | recvEP q =>
    cases q with
    | nil => cases block <;> exact ikp_of_ik ik_fail σ
    | cons dest q =>
      cases block
      all_goals
        intro h0 y hy
        obtain ⟨⟨z1a, z1⟩, h1', hy⟩ := hy
        have e1 : Rdy z1 := rd_tcbEpDequeue dest epptr σ h0 _ h1'
        have v1 : SVK.SVS σ z1 := sv_tcbEpDequeue dest epptr σ _ h1'
        have q1 : SInvQ.T1 z1 := SInvQ.q1_tcbEpDequeue dest epptr σ h1 _ h1'
        obtain ⟨z2, h2, hy⟩ := hy
        obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet h2
        dsimp only at hy
        revert hy
        cases hxs : x.tcbState with
        | blockedOnReceive e r d =>
          intro hy
          dsimp only at hy
          obtain ⟨z3, h3, hy⟩ := hy
          rw [Set.mem_singleton_iff.1 h3] at hy
          exact rd_sendArm_dT call badge cg cgr cd thread epptr dest r z1 e1 q1 (simple_svs hA v1)
            (fwd_svs hF v1) (B8d.rT_svs hct v1) (fun h => rdyT_svs (hcd h) v1)
            (fun x' c hx' hc => by
              rw [hx] at hx'; cases hx'
              exact e1.2.2.1 dest x c hx (Or.inr (Or.inr ⟨e, r, d, hxs⟩)) hc) y hy
        | _ => intro hy; first | exact hy.elim | (obtain ⟨_, h, _⟩ := hy; exact h.elim)

end D

section H
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8h

/-- The faulting thread's bundle, `t` possibly unbound. -/
def HBT (t : ObjRef) (s : State Unit) : Prop :=
  Rdy s ∧ B8d.RT s t ∧ T1 s ∧ Simple s ∧ SInvB.ScInv s

/-- **`send_fault_ipc`** from `HBT t`, `RdyT t` when donating. -/
theorem rd_sendFaultIpcT (t : ObjRef) (cap : Cap) (ex : Fault) (cd : Bool) (s : State Unit) (h : HBT t s)
    (hcd : cd = true → RdyT s t) :
    ∀ y ∈ (sendFaultIpc (Z := Unit) t cap ex cd s).1, Rdy y.2 := by
  intro y hy
  unfold sendFaultIpc at hy
  cases cap
  case endpointCap r b rs =>
    obtain ⟨w1, hw1, hy⟩ := hy
    have r1 : Rdy w1.2 := rd_threadSet_rt (fun tcb => { tcb with tcbFault := some ex }) t s (fun _ => rfl)
      (fun _ => rfl) h.2.1 h.1 w1 hw1
    obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hw1
    obtain ⟨f1, f2, f3⟩ := fh_factsT hx (x' := { x with tcbFault := some ex }) (s' := w1.2) (by rw [e])
      (by rw [e]) (by rw [e]) rfl rfl rfl h.2.1 h.2.2.1 h.2.2.2.2.1.2
    have hd1 : cd = true → RdyT w1.2 t := fun hc =>
      (fh_facts hx (x' := { x with tcbFault := some ex }) (s' := w1.2) (by rw [e])
        (by rw [e]) (by rw [e]) rfl rfl rfl (hcd hc) h.2.2.1 h.2.2.2.2.1.2).1
    have hA : Simple w1.2 := by rw [e]; exact h.2.2.2.1
    obtain ⟨w2, hw2, hy⟩ := hy
    have r2 := rd_sendIpc_dT true false _ _ _ cd t _ w1.2 f1 hd1 f2 hA f3 r1 w2 hw2
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact r2
  case nullCap => rw [Set.mem_singleton_iff.1 hy]; exact h.1
  all_goals exact hy.elim

/-- **`handle_fault t ex`** from `HBT t` (`t` possibly unbound). -/
theorem rd_hfT (t : ObjRef) (ex : Fault) (s : State Unit) (h : HBT t s) :
    ∀ z ∈ (handleFault (Z := Unit) t ex s).1, Rdy z.2 := by
  intro z hz
  unfold handleFault at hz
  obtain ⟨w0, hw0, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hw0
  obtain ⟨⟨cap, s1⟩, hw1, hz⟩ := hz
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hw1
  simp only at e1; subst e1
  obtain ⟨w2, hw2, hz⟩ := hz
  obtain ⟨xt, hxt, rfl⟩ := q1_mem_threadGet hw2
  obtain ⟨⟨b, s3⟩, hw3, hz⟩ := hz
  have hcd : decide (xt.tcbSchedContext ≠ none) = true → RdyT s1 t := by
    intro hd
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (of_decide_eq_true hd)
    exact h.2.1 xt c hxt hc
  have r3 : Rdy s3 := rd_sendFaultIpcT t cap ex _ s1 h hcd _ hw3
  obtain ⟨w4, hw4, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hz
  unfold NonDet.unless at hw4
  split_ifs at hw4
  · rw [Set.mem_singleton_iff.1 hw4]; exact r3
  · unfold handleNoFault at hw4
    exact rd_setThreadState t .inactive trivial s3 r3 w4 hw4

/-! ## `handle_recv` without `RdyT ct` -/

/-- The receiver's facts at a state of `handle_recv` (rd8h's `RH` without
`RdyT C`). -/
def RHT (C : ObjRef) (s : State Unit) : Prop :=
  B8e.RcvS s C ∧ SInvQ.RBk true s ∧ s.curThread = C

theorem rht_asUser (C t : ObjRef) (r : Register) : IK (RHT C) (asUser (Z := Unit) t (getRegister r)) := by
  intro s hs z hz
  obtain ⟨⟨hR, h1, hI, hA, hq, hrq, ⟨x, hx, hnb⟩, hT⟩, hB, hc⟩ := hs
  have v := SVK.sv_asUser' t _ s z hz
  have qc : (QC C z.2 ∧ z.2.curThread = C) :=
    (show IK (fun s : State Unit => QC C s ∧ s.curThread = C) (asUser (Z := Unit) t (getRegister r)) by
      unfold asUser; repeat' (first | ik_step0 | ik_unfold)) s ⟨⟨hq, hrq⟩, hc⟩ z hz
  obtain ⟨x', hx', hs', -⟩ := tcb_tv hx (B8d.tv_asUser t _ s rfl z hz)
  exact ⟨⟨rd_asUser t _ s hR z hz, q1_asUser t _ s h1 z hz,
    SInvB.sik_of_sbk (fun _ => SInvB.sb_asUser _ _) s hI z hz, B8d.simple_svs hA v, qc.1.1, qc.1.2,
    ⟨x', hx', by rw [hs']; exact hnb⟩, B8d.rT_svs hT v⟩, SInvQ.rb_asUser t _ s hB z hz, qc.2⟩

theorem rht_lookupReply (C : ObjRef) : IKE (RHT C) (lookupReply (Z := Unit)) := by
  unfold lookupReply
  repeat' (first | (with_reducible exact rht_asUser _ _ _) |
    (with_reducible exact SInvQ.pk_capFaultLookupCap _ _ _ _) | ik_step0 | ik_unfold)

/-- **`handle_recv` keeps `Rdy`** from `RHT C` (ct possibly unbound). -/
theorem rd_handleRecvT (C : ObjRef) (blk canReply : Bool) :
    SInv.HK (RHT C) Rdy (handleRecv (Z := Unit) blk canReply) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (RHT C) m := fun h => SInvQ.ik_of_ro h
  have hRIP : ∀ cp rc, SInv.HK (RHT C) Rdy (receiveIpc (Z := Unit) C cp blk rc) :=
    fun cp rc s hs y hy => B8e.rd_receiveIpc C cp blk rc s hs.1 hs.2.1 hs.2.2 hy
  have hRS : ∀ cp, SInv.HK (RHT C) Rdy (receiveSignal (Z := Unit) C cp blk) := by
    intro cp s hs y hy
    obtain ⟨⟨hR, -, -, hA, hq, hrq, ⟨x, hx, hnb⟩, hT⟩, -, -⟩ := hs
    exact rd_receiveSignal C cp blk s hR hx hnb hT ⟨hq, hrq⟩ hA hy
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = C := hσ.2.2
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : RHT C y2.2 := (?_ : IK (RHT C) _) σ hσ y2 h2
  · refine hk_catch (I := RHT C) (Q0 := Rdy) ?_ (fun e => ?_) y2.2 hb2 y hy
    · refine hkr_bind (SInvQ.pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (rht_lookupReply C) (fun rc => ?_)
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
      obtain ⟨⟨hR, h1, hI, hA, -, -, -, hT⟩, -, -⟩ := hs
      exact rd_hfT C e s ⟨hR, hT, h1, hA, hI⟩ z hz
  · repeat' (first | exact rht_asUser C _ _ | ik_step0)

end H

end

end Fl4Proofs.P3.SInvR.B8m
