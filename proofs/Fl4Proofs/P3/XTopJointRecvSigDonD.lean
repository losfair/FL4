/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch25 (d1)): **the
notification receive donating an SC to the running current thread** at a
`chooseNewThread` mid state where ct has no SC (`MidN`), i.e. the `SigDon`
case left open by sch23b (XTopJointRecvSigN).

ct receives from an active notification `n` whose SC is bound to no thread:
the badge goes to ct's badge register, `n` becomes idle, then
`maybe_donate_sched_context` / `maybeDonateSc` binds `n`'s SC to ct
(`schedcontext::donate` / `schedContextDonate`) and resumes it
(`schedcontext::resume` / `schedContextResume`: ct, runnable and in no queue,
is postponed into the release queue unless the head refill is ready and
sufficient), then the sporadic `refill_unblock_check` on ct's (new) SC when it
is not the current SC. Unlike the wake-ups of ScSignalDonJ the donee is the
running thread, so there is no `possible_switch_to` and ct's state is any
runnable state. The proofs reuse the wake machinery, which is generic in the
donee:

* `recvCheck_eq` / `recvCheck_of`: FL4's check after the donation in
  `receive_signal` (`rustRecvTail`'s tail: compare with the current SC, then
  `sc_sporadic`) is `notification.unblock_sporadic` (both orders of two pure
  reads).
* `P1.notification.recv_donate_tail.foot` (P1 side): the notification's
  state word then `rustRecvTail` write inside `KW` when the threads sit on the
  notification SC's core (`DonCore`), from P1's
  `maybe_donate_sched_context.tinvF` and `unblock_sporadic.kw`; core 0's
  debug word is then kept (`JAtZ.kw_dbg`).
* `Sched.recv_tailDN` (spec side): `donate_dfr` (IpcSignalDonFr; `t` in no
  queue and not IPC-blocked), `Inv.donate`, `ActIdle.donate`,
  `unblock_frameS`, `Inv.unblockTail`: `Inv`, `BlockedScActive`, the frame
  `DWFr`, `ActIdle`, the action kept, `CurRunM`.
* `Ipc.recvTail_irelD` (FL4 on `IRel`): IpcSignalDon's `donate_irelF`, then
  `unblock_irel` / `unblock_sporadic_kfoot`.
* `JAtZ.recvSigDonJN`: every active-notification receive at a `MidN` state,
  donating or not: the badge write at `J` (`regWrJ`), then `wake_postD`
  (ScSignalDonJ) from there with the frame `NFr` (idle) then `DWFr`.
* `jRecvSigHypDN`: every `receive_signal` at a `MidN` state (no `¬ SigDon`).
-/
import Fl4Proofs.P3.XTopJointRecvSigN
import Fl4Proofs.P3.ScSignalDonJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- FL4's check after the donation in `receive_signal` is `unblock_sporadic`
(module docstring). -/
theorem recvCheck_eq (s : S) (a : A) (t : U64) :
    (do
      let i ← obj.Tcb.sc st t s
      let s4 ← sched.cur_sc st s
      let b1 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i s4
      if b1
      then
        let b2 ← sporadic.sc_sporadic st s i
        if b2
        then
          let s5 ← sporadic.unblock_check st s i
          ok (s5, a)
        else ok (s, a)
      else ok (s, a) : Result (S × A)) =
    (do let s' ← notification.unblock_sporadic st s t; ok (s', a)) := by
  unfold notification.unblock_sporadic
  rw [spec_eq_ok (P1.obj.Tcb.sc.spec s t), spec_eq_ok (Sched.sched.cur_sc.spec' s)]
  simp only [bind_ok, Sched.sc_ne_eq]
  rw [spec_eq_ok (Sched.sporadic.sc_sporadic.spec' s _)]
  simp only [bind_ok]
  split_ifs <;> simp

theorem recvCheck_of {P : S → Prop} (s : S) (a : A) (t : U64)
    (h : notification.unblock_sporadic st s t ⦃ P ⦄) :
    (do
      let i ← obj.Tcb.sc st t s
      let s4 ← sched.cur_sc st s
      let b1 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i s4
      if b1
      then
        let b2 ← sporadic.sc_sporadic st s i
        if b2
        then
          let s5 ← sporadic.unblock_check st s i
          ok (s5, a)
        else ok (s, a)
      else ok (s, a) : Result (S × A)) ⦃ r => r.2 = a ∧ P r.1 ⦄ := by
  rw [recvCheck_eq]
  exact WP.spec_bind h fun s' hs' => (WP.spec_ok _).2 ⟨rfl, hs'⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac Es : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The footprint of `receive_signal`'s active tail** (module docstring):
the notification made idle, then `rustRecvTail`, inside `KW` when the threads
sit on the notification SC's core. -/
theorem notification.recv_donate_tail.foot {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hnN : n ∈ Nt) (hn : H n = some .ntfn) (hEs : n ∈ Es) (hact : L.epState s n = 2#u64) :
    (do
      let s2 ← obj.Ntfn.set_state st n s obj.NTFN_IDLE
      Fl4Proofs.P3.Notif.rustRecvTail st ar s2 a t n) ⦃ r =>
      DonCore st T Scs n s → Foot st T Cs Sg Scs Z Es s r.1 ⦄ := by
  have ht := hc.mem
  have hnΩ : ntfnScA n ∈ Ω := hSg.sub _ (hX.1.ntW n hnN)
  have hdA : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scA t) = 0#u64 → Sch st s t → L.mem s (ntfnScA n) ∈ Ac := by
    intro _ h0 hS'
    exfalso
    rcases hS' with e | e | e | e | ⟨e1, e2⟩ | e
    · exact e hc.nq
    · exact e hc.nr
    · exact hc.na e
    · exact hc.ni e
    · exact hB.resume e1 (by rw [e2]; exact h0)
    · rcases e with e | e
      · exact hc.nb e
      · exact hc.nrp e
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, -, -⟩ := hEW.1 n he
  refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s2 e2 => ?_
  subst e2
  have F0 : Foot st T Cs Sg Scs Z Es s
      (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) :=
    Foot.of (writesIn_wr (ep_aligned hE).2) fun b hb => kw_ep hEs (Or.inr hb)
  obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, ea2, ei2, ec2⟩ := ntfn_idle_all h hB hX hS hSg hn hact
  set s2 := L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs2
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact f2 t ht _ (by simp) (by simp) (by simp) (by simp)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact f2 t ht _ (by simp) (by simp) (by simp) (by simp)
  have st2 : L.mem s2 (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact f2 t ht _ (by simp) (by simp) (by simp) (by simp)
  have hc2 : L.mem s2 (ntfnScA n) = L.mem s (ntfnScA n) := o2 _ hnΩ
  obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
  have hDC : DonCore st T Scs n s → DonCore st T Scs n s2 := fun hD =>
    hD.keep hc2 (fun y hy => by rw [affA_eq]; exact f2 y hy _ (by simp) (by simp) (by simp) (by simp))
      (fun x hx => o2 _ (hcΩ x hx).2.1)
  unfold Fl4Proofs.P3.Notif.rustRecvTail
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinvF (Es := Es) hA s2 a t n Q R h2 hB2 hX2 hS2
    hSg2 ht (by rw [iq2]; exact hc.nq) (by rw [iq2]; exact hc.nr) (by rw [ea2]; exact hc.na)
    (by rw [ei2]; exact hc.ni) fun h0 _ h0t => ?_) ?_
  · rw [hc2] at h0 ⊢
    obtain ⟨c1, -⟩ := hX.2.2.nsc n hnN h0
    refine ⟨c1, by rw [o2 _ (hcΩ _ c1).2.1]; exact hX.2.2.core _ c1, fun hS2t => hdA h0 (by rw [← sc2]; exact h0t) ?_⟩
    exact Sch.of_eq (fun hf => by rwa [iq2] at hf) (fun hf => by rwa [iq2] at hf) ea2 ei2 ec2 st2 hS2t
  rintro ⟨s3, a1⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, -, F3⟩
  refine WP.spec_mono (Fl4Proofs.P3.recvCheck_of s3 a1 t
    (notification.unblock_sporadic.kw (Es := Es) s3 t h3 hX3 hS3 ht)) ?_
  rintro r ⟨-, hr⟩ hD
  exact F0.trans ((F3 (hDC hD)).trans hr)

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

theorem ipcQ_of_runnable {ts : ThreadState} (h : runnable ts = true) : ipcQueuedThreadState ts = false := by
  cases ts <;> simp_all [runnable, ipcQueuedThreadState]

set_option maxHeartbeats 8000000 in
/-- **The receive's tail with or without a donation to the running thread**
(module docstring): `wake_tailD` without the switch, `t` any runnable
thread in no queue. -/
theorem recv_tailDN {σ2 σd σ' : State Unit} {r t : ObjRef} {x2 : Tcb} {xn : Notification}
    (hI : Inv σ2) (hB : BlockedScActive σ2) (hAI : ActIdle σ2)
    (hcur : σ2.schedulerAction = .chooseNewThread ∨ CurInv σ2) (hrun : CurRunM σ2)
    (hk : σ2.kheap t = some (.tcb x2)) (hxr : runnable x2.tcbState = true)
    (hkn : σ2.kheap r = some (.notification xn)) (hnq : NotQueued σ2 t) (hoff : OffOK σ2)
    (hsp : ∀ c y k, σ2.kheap c = some (.schedContext y k) → y.scSporadic = true → scActive y = true)
    (hD : maybeDonateSc (Z := Unit) t r σ2 = ({((), σd)}, False))
    (hm : ((), σ') ∈ (specUnblock t σd).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ DWFr r t σ2 σ' ∧ ActIdle σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurRunM σ' ∧
      σ'.schedulerAction = σ2.schedulerAction := by
  have hnipc : ∀ x, σ2.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = false := fun x hx => by
    rw [hk] at hx; cases hx; exact ipcQ_of_runnable hxr
  obtain ⟨Fd, had, -, -, Bd⟩ := donate_dfr (r := r) hI hk hkn hnq hoff hB hnipc hD
  obtain ⟨Id, hrq⟩ := Inv.donate hI hk hkn hxr hnq hD
  obtain ⟨xd, hkd⟩ : ∃ xd, σd.kheap t = some (.tcb xd) := by
    obtain ⟨st, bn, fl, ar, sc, hkd, -⟩ := Fd.tcbF hk
    exact ⟨_, hkd⟩
  have hsad : ∀ p y k, xd.tcbSchedContext = some p → σd.kheap p = some (.schedContext y k) →
      y.scSporadic = true → scActive y = true := by
    intro p y k _ hky hs
    obtain ⟨y0, rf, nt, tc, hy0, rfl, -⟩ := Fd.scB hky
    exact hsp p y0 k hy0 hs
  obtain ⟨F5, ha5⟩ := unblock_frameS Id hkd hsad hm r
  have FF : DWFr r t σ2 σ' := Fd.trans (DWFr.ofNFr F5)
  have hI' : Inv σ' := Id.unblockTail hkd (fun p y n hp hky hm' => hrq xd p y n hkd hp hky hm') hsad hm
  have hact : σ'.schedulerAction = σ2.schedulerAction := by rw [ha5, had]
  refine ⟨hI', F5.bsa Bd, FF, ⟨fun u hu => FF.sched (hAI.1 u (by rw [← hact]; exact hu)), FF.idleOK hAI.2⟩,
    ?_, ?_, hact⟩
  · rcases hcur with e | hC
    · exact Or.inl (hact.trans e)
    · exact Or.inr (FF.curInv hC)
  · exact hrun.of_act FF.curRunW fun e => by rw [hact]; exact e

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **FL4's active-receive tail on `IRel`, donating or not** (module
docstring): `donate_irelF`, then the check as `unblock_sporadic`. -/
theorem recvTail_irelD (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t n : U64} (ht : t ∈ T)
    (hn : n ∈ N) (hD : DonOK st C s σ t n) :
    rustRecvTail st ar s a t n ⦃ r => r.2 = a ∧ ∃ σd σ',
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σd)}, False) ∧
      specUnblock t.bv σd = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ IFrame (L := L) th s r.1 ∧ FinStep (st := st) T N C c s σ r.1 σ' ⦄ := by
  unfold rustRecvTail
  refine WP.spec_bind (donate_irelF hP0 hmb s a σ hX ht hn hD) ?_
  rintro ⟨s4, a4⟩ ⟨ea4, σd, hd, hX4, hSS4, hTW4, -⟩
  simp only at ea4
  subst ea4
  refine WP.spec_mono (recvCheck_of s4 _ t
    (WP.spec_and (unblock_irel hP0 s4 σd hX4 t ht) (unblock_sporadic_kfoot hX4.2.2.1 t ht))) ?_
  rintro ⟨s6, a6⟩ ⟨ea6, ⟨σ6, hu, hf6, hv6, hX6⟩, hw6⟩
  try simp only at ea6 hu hf6 hv6 hX6 hw6
  have hSS6 : IFrame (L := L) th s4 s6 := IRel.iframe_of hX4 hw6 fun b hb => tfoot_oobj hX4.2.2.1 (Or.inl hb)
  have hTW6 : FinStep (st := st) T N C c s4 σd s6 σ6 := by
    refine ⟨hw6.mono fun b hb => Or.inl hb, SzKeepC.of fun p y k hp => ?_⟩
    have hmem : ((), σ6) ∈ ((Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) σd).1 := by
      rw [show (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) = specUnblock t.bv from rfl, hu]
      exact Set.mem_singleton _
    obtain ⟨y0, h0, -, -⟩ := MaxK.mk_unblock t.bv σd ((), σ6) hmem p y k hp
    exact ⟨y0, h0⟩
  exact ⟨ea6, σd, σ6, hd, hu, hX6, hSS4.trans hSS6, hTW4.trans hTW6⟩

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 32000000 in
/-- **Receiving from an active notification at a `MidN` state, donating or
not** (module docstring). -/
theorem JAtZ.recvSigDonJN (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : MidN σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (blk : Bool) (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n blk ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
  have hsc0 : xt.tcbSchedContext = none := hni.2.2.2 xt (by rw [hcur]; exact hkt)
  have hrn : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hcb := J.canBlockCurMN ht hcur hkt hrn hni.1 (J.inv.notRel_of_noSc hkt hsc0) hni hnq
  have hx := hI.1.toN.at_ntfn hn hk
  have hst : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active (T := Z.T) (hact ▸ hx.obj) rfl
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
  -- P1's `BlkOK` after the whole receive
  obtain ⟨⟨Q0, R0, h0'⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have p1 := P1.notification.receive_signal.ipc hAT s a t n blk Q0 R0 h0' hB0 hX0 hS0 hSg0 hcb
    hHn hHn (by rw [epState_eq, hst, ntfn_consts.2.2]; decide)
  -- the badge register at `J`
  have hXb := badge_wr_irel J.ip hI ht hkt (L.mem s (nBadgeA n))
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ ht hkt Fl4Spec.badge_register _ hXb
  rw [hb0, regIdx_badge] at J1
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  set xt1 := setReg xt Fl4Spec.badge_register b0 with hxt1
  set σ1 := updK σ t.bv (.tcb xt1) with hσ1
  set s1 := L.wr s (regA t layout.reg.BADGE) (L.mem s (nBadgeA n)) with hs1
  have hk1 : σ1.kheap n.bv = some (.notification x) := by simp [hσ1, updK, hnt, hk]
  have hkt1 : σ1.kheap t.bv = some (.tcb xt1) := by simp [hσ1, updK]
  have hcur1 : σ1.curThread = t.bv := hcur
  have hrn1 : Fl4Spec.runnable xt1.tcbState = true := hrn
  have hsc1 : xt1.tcbSchedContext = none := hsc0
  have hni1 : MidN σ1 := ⟨hni.1, fun y hy => by rw [hcur1, hkt1] at hy; cases hy; exact hrn1, hni.2.2.1,
    fun y hy => by rw [hcur1, hkt1] at hy; cases hy; exact hsc1⟩
  have hnq1 : ∀ d p, σ1.curThread ∉ σ1.readyQueues d p := hnq
  have hnr1 : t.bv ∉ σ1.releaseQueue := J1.inv.notRel_of_noSc hkt1 hsc1
  have hcb1 := J1.canBlockCurMN ht hcur1 hkt1 hrn1 hni1.1 hnr1 hni1 hnq1
  -- the notification's state, FL4 on `IRel` from `J1`
  have hI1 := J1.xtop.irelK J1.ks J1.buf
  have hx1 := hI1.1.toN.at_ntfn hn hk1
  have hst1 : stOf (L.mem s1) n = obj.NTFN_ACTIVE := stOf_active (T := Z.T) (hact ▸ hx1.obj) rfl
  obtain ⟨hR2, hW2, hS2⟩ := set_idle_relI J1.ip hI1.1 hn hk1 hact
  set σ2 := updK σ1 n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x)) with hσ2
  set s2 := L.wr s1 (P1.epTSA n) ((L.mem s1 (P1.epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs2
  have hP := J1.ip.e
  have hSRT2 := hI1.2
  have hX2 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s2 σ2 :=
    ⟨hR2, hSRT2.1.stableN hSRT2.2.1.placed hW2 hS2, hSRT2.2.1.stable hW2 hS2,
      hSRT2.2.2.mono hW2.1 (SzKeep.ntfnStep hS2)⟩
  have hSS2 : IFrame (L := L) Z.th s1 s2 :=
    IRel.iframe_of hI1 hW2 fun b hb => iwords_oobj (NWrite.iwords hP.tcb hb)
  have hTW2 : FinStep (st := st) Z.T Z.N Z.C Z.c s1 σ1 s2 σ2 :=
    ⟨hW2.mono fun b hb => NWrite.finW hP.tcb hb, SzKeepC.of (SzKeep.ntfnStep hS2)⟩
  -- the spec at the state after the notification write
  have hN0 : NObj x.ntfnObj (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x).ntfnObj :=
    Or.inr ⟨fun l h => (by rw [hact] at h; cases h), fun l h => (by cases h)⟩
  have F1 : NFr true n.bv σ1 σ2 := NFr.upd hk1 (Or.inr (Or.inr ⟨x, _, rfl, rfl, rfl, hN0.queue, fun _ => hN0,
    Or.inl rfl, fun _ => hN0, Or.inl rfl⟩))
  have I2 : Inv σ2 := J1.inv.updNtfn hk1 fun p hp => J1.inv.ntfnSc n.bv x p hk1 hp
  have hN2 : NSC Z.N Z.C σ2 := J1.nsc.step hS2
  have hkt2 : σ2.kheap t.bv = some (.tcb xt1) := by
    simp only [hσ2, updK, Function.update_of_ne hnt.symm]; exact hkt1
  have hkn2 : σ2.kheap n.bv = some (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x)) := by
    simp [hσ2, updK]
  have hDon : DonOK st Z.C s2 σ2 t n :=
    ⟨I2.relOK, fun h0 => NSC.mem hN2 hR2.toN hn h0, fun _ y _ => by rw [← hcur]; exact hnq _ _,
      I2.actReady⟩
  -- FL4: the run from `s` with the two P3 views of the tail
  obtain ⟨⟨Q1, R1, h1q⟩, hB1, hX1, hS1, hSg1⟩ := J1.blk
  have hfootT := P1.notification.recv_donate_tail.foot (Es := P1.EH H) hAT s1 a t n Q1 R1
    h1q hB1 hX1 hS1 hSg1 hcb1 hHn hHn (Or.inr hHn)
    (by rw [epState_eq, hst1, ntfn_consts.2.2])
  have hirT : (do
      let s2 ← obj.Ntfn.set_state st n s1 obj.NTFN_IDLE
      rustRecvTail st arI s2 a t n) ⦃ r => r.2 = a ∧ ∃ σd σ',
        Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ2 = ({((), σd)}, False) ∧
        specUnblock t.bv σd = ({((), σ')}, False) ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.1 σ' ∧
        IFrame (L := L) Z.th s1 r.1 ∧ FinStep (st := st) Z.T Z.N Z.C Z.c s1 σ1 r.1 σ' ⦄ := by
    refine WP.spec_bind (P1.obj.Ntfn.set_state.val _ n obj.NTFN_IDLE) ?_
    rintro s2' rfl
    refine WP.spec_mono (recvTail_irelD J1.ip hmb s2 a σ2 hX2 ht hn hDon) ?_
    rintro r ⟨hra, σd, σ', hd, hu, hX', hSS', hTW'⟩
    exact ⟨hra, σd, σ', hd, hu, hX', hSS2.trans hSS', hTW2.trans hTW'⟩
  have hmain : notification.receive_signal st arI s a t n blk ⦃ r => r.2 = a ∧ (P1.DonCore st (P1.Heap.tcbs H)
      (P1.Heap.scs H) n s1 → P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
        (P1.EH H) s1 r.1) ∧ ∃ σd σ',
        Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ2 = ({((), σd)}, False) ∧
        specUnblock t.bv σd = ({((), σ')}, False) ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.1 σ' ∧
        IFrame (L := L) Z.th s1 r.1 ∧ FinStep (st := st) Z.T Z.N Z.C Z.c s1 σ1 r.1 σ' ⦄ := by
    unfold notification.receive_signal
    refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
    rintro v rfl
    rw [epState_eq, hst, if_neg (by rw [ntfn_consts.1, ntfn_consts.2.2]; decide),
      if_neg (by rw [ntfn_consts.2.1, ntfn_consts.2.2]; decide)]
    refine WP.spec_bind (obj.Ntfn.badge.spec s n) ?_
    rintro bb rfl
    refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE _) ?_
    rintro s1' rfl
    exact WP.spec_mono (WP.spec_and hfootT hirT) fun r ⟨hf, hra, hR⟩ => ⟨hra, hf, hR⟩
  refine WP.spec_mono (WP.spec_and hmain p1) ?_
  rintro ⟨s', a'⟩ ⟨⟨hra, hfoot, σd, σ', hd, hu, hIR, hF, hFS⟩, hbk⟩
  simp only [WP.uncurry'_pair] at hbk hra hfoot hIR hF hFS
  subst hra
  -- the spec's side
  have hsp2 : ∀ c y k, σ2.kheap c = some (.schedContext y k) → y.scSporadic = true → Fl4Spec.scActive y = true := by
    intro c y k hc
    have hcn : c ≠ n.bv := by rintro rfl; rw [hkn2] at hc; cases hc
    have hct : c ≠ t.bv := by rintro rfl; rw [hkt2] at hc; cases hc
    have hc0 : σ.kheap c = some (.schedContext y k) := by
      simpa [hσ2, hσ1, updK, hcn, hct] using hc
    exact J.sv.scSpor c y k hc0
  have hnqT : NotQueued σ2 t.bv := ⟨fun d p => by rw [← hcur]; exact hnq d p, hnr1⟩
  obtain ⟨I', B', FF, AI', cur', run', -⟩ := recv_tailDN (r := n.bv) I2 (F1.bsa J1.bsa)
    ⟨fun u hu => F1.sched (J1.act.1 u hu), F1.idleOK J1.act.2⟩ (Or.imp id F1.curInv J1.cur)
    (Or.imp id F1.curRunW J1.curRun) hkt2 hrn1 hkn2 hnqT (F1.off J1.off) hsp2 hd
    (by rw [hu]; exact Set.mem_singleton _)
  -- `JAtZ` after, from `J1`
  have hw : P1.WritesIn st s1 s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s1 σ1) :=
    hFS.1.mono fun b h => Or.inl h
  have hRR : ∀ q ∈ Z.R, ∀ xr, σ1.kheap q.bv = some (.reply xr) → xr.replyTcb = some t.bv →
      Detached Z.C Lst q ∧ L.mem s1 (rNextA q) = 0#u64 ∧ L.mem s1 (rPrevA q) = 0#u64 := by
    intro q _ xr hq hxt
    exfalso
    obtain ⟨x', hk', hs'⟩ := J1.sv.replyTcb q.bv xr t.bv hq hxt
    rw [hkt1] at hk'; cases hk'
    rcases hs' with e | ⟨ep, dd, e⟩ <;> rw [e] at hrn1 <;> cases hrn1
  have htD := J1.not_dead_of_st ht hkt1 (by rcases runnable_code hrn1 with h | h | h <;> rw [h] <;> decide)
  obtain ⟨V', J'⟩ := J1.wake_postD hIR hF hw hbk (hfoot (J1.donCore hn)) ((DWFr.ofNFr F1.weak).trans FF) I' B'
    AI' cur' run' hRR htD ⟨t, ht, rfl⟩
  -- the spec's outcome
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ =
      specRecvTail t.bv n.bv σ2 := by
    rw [receiveSignal_cap hk]
    simp only [hact]
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt), nd_bind_one (setNotification_eq _ hk1)]
  have hsT : specRecvTail t.bv n.bv σ2 = specUnblock t.bv σd := by
    unfold specRecvTail; rw [nd_bind_one hd]; rfl
  rw [hspec, hsT, hu]
  exact ⟨_, Set.mem_singleton _, J'.xtop.relTop, _, _, _, _, _, _, J'⟩

set_option maxHeartbeats 4000000 in
/-- **Every notification receive at a `MidN` state** (module docstring):
XTopJointRecvSigN's `jRecvSigHypN_of` without `¬ SigDon`. -/
theorem jRecvSigHypDN (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidN σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p : U64) (b : U64) (w rd : Bool) (ac : Fl4Spec.Cap) (hcr : CapRel (.Notification p b w rd) ac)
    (hex : ∃ x, σ.kheap p.bv = some (.notification x)) (hHd : JHeld (L := L) Z.th s (.Notification p b w rd)) :
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  by_cases hdon : SigDon σ p.bv
  · obtain ⟨x, hk⟩ := hex
    have hac : ac = absCap (.Notification p b w rd) := hcr.abs
    subst hac
    obtain ⟨n, hn, h⟩ := J.obj.ntfn _ x hk
    rw [Sched.bv_inj h] at hn
    obtain ⟨x', hk', ⟨b0, hact⟩, -⟩ := hdon
    rw [hk] at hk'; cases hk'
    exact WP.spec_mono (J.recvSigDonJN hAT hmb ht hcur hni hnq hn hk hact true b.bv (rightsOf w rd false false))
      fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ => ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  · exact jRecvSigHypN_of hAT J ht hcur hni hsw hnq p b w rd ac hcr hex hHd hdon

end

end

end Fl4Proofs.P3
