/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch27 (1)): **the
endpoint receive whose bound notification donates an SC to the running
current thread** (`IpcActDon`, XTopJointRecvIpcN) at a `chooseNewThread`
mid state where ct has no SC (`MidN`).

`receive_ipc` with ct's bound notification active is `complete_signal`
(XTopJointRecvIpcAct's `receive_ipc_preA` / `receiveIpc_active`): the badge
write, the notification made idle, `maybe_donate_sched_context` /
`maybeDonateSc`, then the complete check (sporadic, ct's SC is the
notification's, not the current SC, `refill_unblock_check`). Where ct had no
SC, after the donation ct's SC is `none` or the notification's SC, so the
complete check is the receive check of `receive_signal`
(XTopJointRecvSigDonD), and sch25's machinery applies unchanged:

* `Sched.donate_kh` (spec): `maybeDonateSc t n` for an SC-less `t` keeps
  the heap or makes it `donSt` of the notification's SC; `donShape_of`:
  then ct's SC is `none` or the notification's (`DonShape`).
* `specCompleteCheck_eqU` (spec): under `DonShape`, ScTails'
  `specCompleteCheck` is `specUnblock`.
* `completeCheck_eq` (FL4): under `scA t = 0 ∨ scA t = nScA n` the complete
  check is the receive check; `completeCheck_of`: without that, the complete
  check does nothing or what `unblock_sporadic` does.
* `P1.notification.complete_donate_tail.foot`: P1's
  `recv_donate_tail.foot` for `rustCompleteTail` (by `completeCheck_of`).
* `Ipc.completeTail_irelD`: `recvTail_irelD` for `rustCompleteTail` (the
  FL4 shape from the spec's through `SchedRel` / `NtfnStateRel`).
* `JAtZ.recvIpcActDJN`: `recvSigDonJN` with `complete_signal`; BlkOK from
  P1's `complete_signal.ipc`.
* `jRecvIpcUDN`: `jRecvIpcUN` without `¬ IpcActDon`; `jRecvIpcLinkDN`:
  XTopJointRecvIpcLinkN's `jRecvIpcLinkN` without it.
-/
import Fl4Proofs.P3.XTopJointRecvSigDonD
import Fl4Proofs.P3.XTopJointRecvIpcN
import Fl4Proofs.P3.XTopJointRecvIpcLinkN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- **`maybeDonateSc` for an SC-less thread: nothing, or `donSt`** (module
docstring). -/
theorem donate_kh {σ σ' : State Unit} (h : Inv σ) {t n : ObjRef} {xt : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn)) (hnq : NotQueued σ t)
    (h0 : xt.tcbSchedContext = none)
    (he : maybeDonateSc (Z := Unit) t n σ = ({((), σ')}, False)) :
    σ'.kheap = σ.kheap ∨ ∃ p ys ns, xn.ntfnSc = some p ∧ σ.kheap p = some (.schedContext ys ns) ∧
      σ'.kheap = (donSt σ p t ys ns xt).kheap := by
  unfold maybeDonateSc getTcbObjRef at he
  rw [nd_bind_one (threadGet_eq _ hkt)] at he
  simp only [NonDet.when] at he
  rw [if_pos h0] at he
  rw [nd_bind_one' (getNtfnSc_eq hkn)] at he
  cases hsc : xn.ntfnSc with
  | none => rw [hsc] at he; rw [pair_eq he]; exact Or.inl rfl
  | some p =>
    rw [hsc] at he
    obtain ⟨ys, ns, hks⟩ := h.ntfnSc n xn p hkn hsc
    have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
    simp only [NonDet.maybeM] at he
    have hg : getScObjRef (Z := Unit) SchedContext.scTcb p σ = ({(ys.scTcb, σ)}, False) := by
      unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl
    rw [nd_bind_one hg] at he
    cases hst : ys.scTcb with
    | some u =>
      rw [hst] at he; simp only [NonDet.when, reduceCtorEq, ↓reduceIte] at he; rw [pair_eq he]; exact Or.inl rfl
    | none =>
      rw [hst] at he
      simp only [NonDet.when, ↓reduceIte] at he
      rw [nd_bind_one (schedContextDonate_eq hks hst hkt hpt)] at he
      have hb := h.donated hks hst hkt hpt hnq
      set σd := donSt σ p t ys ns xt with hσd
      set xt' : Tcb := { xt with tcbSchedContext := some p }
      set ys' : SchedContext := { ys with scTcb := some t }
      have kt : σd.kheap t = some (.tcb xt') := by simp [σd, donSt, updK] <;> rfl
      have kp : σd.kheap p = some (.schedContext ys' ns) := by simp [σd, donSt, updK, hpt] <;> rfl
      have hne : scActive ys' = true → ys'.scRefills ≠ [] := h.ne p ys ns hks
      rw [resume_spec_eq kp rfl kt hne
        (fun hs => by
          obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
          rw [kt] at h1; cases h1; cases h2; rw [kp] at h4; cases h4; exact ⟨h3, h5⟩)
        (fun _ => hnq.1 _ _)] at he
      split_ifs at he with hc
      · have hact : scActive ys' = true := by
          obtain ⟨x, scp, y, m, h1, h2, -, h4, h5, -⟩ := schedulable_inv hc.1
          rw [kt] at h1; cases h1; cases h2; rw [kp] at h4; cases h4; exact h5
        obtain ⟨b, hp⟩ := postpone_eq kp rfl kt (specRt σd) (fun u hu => by
          rcases hu with rfl | hu
          · exact ⟨xt', p, ys', ns, kt, rfl, kp, hne hact, specRt_eq kt rfl kp (hne hact)⟩
          · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, h5⟩ := hb.rel u hu
            exact ⟨xu, scp, yu, nu, h1, h2, h4, hb.ne _ _ _ h4 h5, specRt_eq h1 h2 h4 (hb.ne _ _ _ h4 h5)⟩)
        rw [hp] at he
        rw [pair_eq he]
        exact Or.inr ⟨p, ys, ns, rfl, hks, rfl⟩
      · rw [pair_eq he]
        exact Or.inr ⟨p, ys, ns, rfl, hks, rfl⟩

/-- **ct's SC after a donation to an SC-less ct**: `none`, or an SC which
is the notification's. -/
def DonShape (σ : State Unit) (t n : ObjRef) : Prop :=
  ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext = none ∨
    ∃ p y k xn, x.tcbSchedContext = some p ∧ σ.kheap p = some (.schedContext y k) ∧
      σ.kheap n = some (.notification xn) ∧ xn.ntfnSc = some p

theorem donShape_of {σ σ' : State Unit} (h : Inv σ) {t n : ObjRef} {xt : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn)) (hnq : NotQueued σ t)
    (h0 : xt.tcbSchedContext = none)
    (he : maybeDonateSc (Z := Unit) t n σ = ({((), σ')}, False)) : DonShape σ' t n := by
  have hnt : n ≠ t := by rintro rfl; rw [hkt] at hkn; cases hkn
  intro x hx
  rcases donate_kh h hkt hkn hnq h0 he with e | ⟨p, ys, ns, hsc, hks, e⟩
  · rw [e, hkt] at hx; cases hx; exact Or.inl h0
  · have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
    have hpn : n ≠ p := by rintro rfl; rw [hkn] at hks; cases hks
    rw [e] at hx
    simp [donSt, updK] at hx
    subst hx
    refine Or.inr ⟨p, { ys with scTcb := some t }, ns, xn, rfl, ?_, ?_, hsc⟩
    · rw [e]; simp [donSt, updK, hpt]
    · rw [e]; simp [donSt, updK, hnt, hpn, hkn]

/-- **The spec's complete check is `specUnblock` under `DonShape`** (module
docstring). -/
theorem specCompleteCheck_eqU {σ : State Unit} {t n : ObjRef} (hsh : DonShape σ t n)
    {xt : Tcb} (hkt : σ.kheap t = some (.tcb xt)) :
    specCompleteCheck t n σ = specUnblock t σ := by
  unfold specCompleteCheck specUnblock Fl4Spec.getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hkt), nd_bind_one (threadGet_eq _ hkt)]
  rcases hsh xt hkt with h0 | ⟨p, y, k, xn, hp, hky, hkn, hns⟩
  · rw [h0]; rfl
  · rw [hp]
    simp only [NonDet.maybeM, ifCondRefillUnblockCheck]
    rw [nd_bind_one (getSchedContext_eq hky), nd_bind_one (getSchedContext_eq hky)]
    by_cases hs : y.scSporadic = true
    · simp only [NonDet.when, hs, ↓reduceIte, true_and]
      rw [nd_bind_one (getNtfnSc_eq hkn), hns, nd_gets_bind, nd_gets_bind, nd_pure_bind']
      by_cases hc : p ≠ σ.curSc <;> simp [hc]
    · simp only [NonDet.when, hs, ↓reduceIte, false_and, Bool.false_eq_true, nd_gets_bind, nd_pure_bind']

/-- `t` still holds a TCB after the donation. -/
theorem donate_tcb {σ σ' : State Unit} (h : Inv σ) {t n : ObjRef} {xt : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn)) (hnq : NotQueued σ t)
    (h0 : xt.tcbSchedContext = none)
    (he : maybeDonateSc (Z := Unit) t n σ = ({((), σ')}, False)) : ∃ xd, σ'.kheap t = some (.tcb xd) := by
  rcases donate_kh h hkt hkn hnq h0 he with e | ⟨p, ys, ns, -, -, e⟩
  · exact ⟨xt, by rw [e, hkt]⟩
  · exact ⟨_, by rw [e]; simp [donSt, updK] <;> rfl⟩

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P3.Notif

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- FL4's complete check is the receive check when ct's SC is `0` or the
notification's (module docstring). -/
theorem completeCheck_eq (s : S) (a : A) (t n : U64)
    (h : L.mem s (P1.scA t) = 0#u64 ∨ L.mem s (P1.scA t) = L.mem s (nScA n)) :
    (do
      let i1 ← obj.Tcb.sc st t s
      let b2 ← sporadic.sc_sporadic st s i1
      if b2
      then
        let i2 ← obj.Ntfn.sc st n s
        if i1 = i2
        then
          let s4 ← sched.cur_sc st s
          let b3 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i1 s4
          if b3
          then
            let s5 ← sporadic.unblock_check st s i1
            ok (s5, a)
          else ok (s, a)
        else ok (s, a)
      else ok (s, a) : Result (S × A)) =
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
      else ok (s, a) : Result (S × A)) := by
  rw [spec_eq_ok (P1.obj.Tcb.sc.spec s t), spec_eq_ok (Sched.sched.cur_sc.spec' s),
    spec_eq_ok (obj.Ntfn.sc.spec s n)]
  simp only [bind_ok, Sched.sc_ne_eq]
  rw [spec_eq_ok (Sched.sporadic.sc_sporadic.spec' s _)]
  simp only [bind_ok]
  rcases h with h | h
  · rw [h]; simp
  · rw [h]; split_ifs <;> simp_all

/-- FL4's complete check does nothing or what `unblock_sporadic` does. -/
theorem completeCheck_of {P : S → Prop} (s : S) (a : A) (t n : U64)
    (h : notification.unblock_sporadic st s t ⦃ P ⦄) (h0 : P s) :
    (do
      let i1 ← obj.Tcb.sc st t s
      let b2 ← sporadic.sc_sporadic st s i1
      if b2
      then
        let i2 ← obj.Ntfn.sc st n s
        if i1 = i2
        then
          let s4 ← sched.cur_sc st s
          let b3 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i1 s4
          if b3
          then
            let s5 ← sporadic.unblock_check st s i1
            ok (s5, a)
          else ok (s, a)
        else ok (s, a)
      else ok (s, a) : Result (S × A)) ⦃ r => r.2 = a ∧ P r.1 ⦄ := by
  by_cases hc : L.mem s (P1.scA t) = 0#u64 ∨ L.mem s (P1.scA t) = L.mem s (nScA n)
  · rw [completeCheck_eq s a t n hc]
    exact recvCheck_of s a t h
  · push_neg at hc
    rw [spec_eq_ok (P1.obj.Tcb.sc.spec s t), spec_eq_ok (obj.Ntfn.sc.spec s n)]
    simp only [bind_ok]
    rw [spec_eq_ok (Sched.sporadic.sc_sporadic.spec' s _)]
    simp only [bind_ok, hc.2, ↓reduceIte]
    split_ifs <;> exact (WP.spec_ok _).2 ⟨rfl, h0⟩

/-- `completeCheck_eq` at the level of the WP. -/
theorem completeCheck_of_recv {P : S × A → Prop} (s : S) (a : A) (t n : U64)
    (h : L.mem s (P1.scA t) = 0#u64 ∨ L.mem s (P1.scA t) = L.mem s (nScA n))
    (hr : (do
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
      else ok (s, a) : Result (S × A)) ⦃ P ⦄) :
    (do
      let i1 ← obj.Tcb.sc st t s
      let b2 ← sporadic.sc_sporadic st s i1
      if b2
      then
        let i2 ← obj.Ntfn.sc st n s
        if i1 = i2
        then
          let s4 ← sched.cur_sc st s
          let b3 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i1 s4
          if b3
          then
            let s5 ← sporadic.unblock_check st s i1
            ok (s5, a)
          else ok (s, a)
        else ok (s, a)
      else ok (s, a) : Result (S × A)) ⦃ P ⦄ := by
  rw [completeCheck_eq s a t n h]; exact hr

end

end Fl4Proofs.P3

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac Es : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The footprint of `complete_signal`'s active tail** (module docstring):
`recv_donate_tail.foot` for `rustCompleteTail`. -/
theorem notification.complete_donate_tail.foot {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hnN : n ∈ Nt) (hn : H n = some .ntfn) (hEs : n ∈ Es) (hact : L.epState s n = 2#u64) :
    (do
      let s2 ← obj.Ntfn.set_state st n s obj.NTFN_IDLE
      Fl4Proofs.P3.Notif.rustCompleteTail st ar s2 a t n) ⦃ r =>
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
  unfold Fl4Proofs.P3.Notif.rustCompleteTail
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinvF (Es := Es) hA s2 a t n Q R h2 hB2 hX2 hS2
    hSg2 ht (by rw [iq2]; exact hc.nq) (by rw [iq2]; exact hc.nr) (by rw [ea2]; exact hc.na)
    (by rw [ei2]; exact hc.ni) fun h0 _ h0t => ?_) ?_
  · rw [hc2] at h0 ⊢
    obtain ⟨c1, -⟩ := hX.2.2.nsc n hnN h0
    refine ⟨c1, by rw [o2 _ (hcΩ _ c1).2.1]; exact hX.2.2.core _ c1, fun hS2t => hdA h0 (by rw [← sc2]; exact h0t) ?_⟩
    exact Sch.of_eq (fun hf => by rwa [iq2] at hf) (fun hf => by rwa [iq2] at hf) ea2 ei2 ec2 st2 hS2t
  rintro ⟨s3, a1⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, -, F3⟩
  refine WP.spec_mono (Fl4Proofs.P3.completeCheck_of s3 a1 t n
    (notification.unblock_sporadic.kw (Es := Es) s3 t h3 hX3 hS3 ht) (Foot.refl s3)) ?_
  rintro r ⟨-, hr⟩ hD
  exact F0.trans ((F3 (hDC hD)).trans hr)


/-- P1's `complete_signal.ipc` from `CanBlock` (module docstring). -/
theorem notification.complete_signal.ipcC {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n t : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hnN : n ∈ Nt) (hn : H n = some .ntfn) :
    notification.complete_signal st ar s a n t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
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
  exact notification.complete_signal.ipc hA s a n t Q R h hB hX hS hSg hc.mem hc.nq hc.nr hc.na hc.ni hn
    (hSg.sub _ (hX.1.ntW n hnN)) (fun h0 => ⟨(hX.2.2.nsc n hnN h0).1, hX.2.2.core _ (hX.2.2.nsc n hnN h0).1⟩) hdA

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **FL4's active complete tail on `IRel`, donating or not** (module
docstring): `recvTail_irelD` for `rustCompleteTail`, given `DonShape` of
every donation outcome. -/
theorem completeTail_irelD (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {t n : U64} (ht : t ∈ T)
    (hn : n ∈ N) (hD : DonOK st C s σ t n)
    (hsh : ∀ σd, Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σd)}, False) → DonShape σd t.bv n.bv) :
    rustCompleteTail st ar s a t n ⦃ r => r.2 = a ∧ ∃ σd σ',
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σd)}, False) ∧
      specUnblock t.bv σd = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ IFrame (L := L) th s r.1 ∧ FinStep (st := st) T N C c s σ r.1 σ' ⦄ := by
  unfold rustCompleteTail
  refine WP.spec_bind (donate_irelF hP0 hmb s a σ hX ht hn hD) ?_
  rintro ⟨s4, a4⟩ ⟨ea4, σd, hd, hX4, hSS4, hTW4, -⟩
  simp only at ea4
  subst ea4
  have hsh4 : L.mem s4 (P1.scA t) = 0#u64 ∨ L.mem s4 (P1.scA t) = L.mem s4 (nScA n) := by
    obtain ⟨Q, R, hc, hs⟩ := hX4.2.2.1.lists
    obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
    rcases hsh σd hd xt hkt with h0 | ⟨p, y, k, xn, hp, -, hkn, hns⟩
    · exact Or.inl (optRef_none (hsct.symm.trans h0))
    · right
      obtain ⟨xn', hkn', hxn⟩ := hX4.1.toN.ntfn n hn
      rw [hkn] at hkn'; cases hkn'
      exact Sched.optRef_inj.1 (hsct.symm.trans (hp.trans (hns.symm.trans hxn.sc)))
  refine completeCheck_of_recv s4 _ t n hsh4 ?_
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
/-- **`receive_ipc` with an active bound notification at a `MidN` state,
donating or not** (module docstring). -/
theorem JAtZ.recvIpcActDJN (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : MidN σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hbn : xt.tcbBoundNotification = some n.bv) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (blk : Bool) {e : U64} {xe : Fl4Spec.Endpoint} (hke : σ.kheap e.bv = some (.endpoint xe))
    (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hsc0 : xt.tcbSchedContext = none := hni.2.2.2 xt (by rw [hcur]; exact hkt)
  have hrn : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hcb := J.canBlockCurMN ht hcur hkt hrn hni.1 (J.inv.notRel_of_noSc hkt hsc0) hni hnq
  have hx := hI.1.toN.at_ntfn hn hk
  have hst : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active (T := Z.T) (hact ▸ hx.obj) rfl
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
  -- P1's `BlkOK` after `complete_signal`
  obtain ⟨⟨Q0, R0, h0'⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have p1 := P1.notification.complete_signal.ipcC hAT s a n t Q0 R0 h0' hB0 hX0 hS0 hSg0 hcb hHn hHn
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
  have hnqT : NotQueued σ2 t.bv := ⟨fun d p => by rw [← hcur]; exact hnq d p, hnr1⟩
  have hDon : DonOK st Z.C s2 σ2 t n :=
    ⟨I2.relOK, fun h0 => NSC.mem hN2 hR2.toN hn h0, fun _ y _ => by rw [← hcur]; exact hnq _ _,
      I2.actReady⟩
  -- FL4: the run from `s` with the two P3 views of the tail
  obtain ⟨⟨Q1, R1, h1q⟩, hB1, hX1, hS1, hSg1⟩ := J1.blk
  have hfootT := P1.notification.complete_donate_tail.foot (Es := P1.EH H) hAT s1 a t n Q1 R1
    h1q hB1 hX1 hS1 hSg1 hcb1 hHn hHn (Or.inr hHn)
    (by rw [epState_eq, hst1, ntfn_consts.2.2])
  have hirT : (do
      let s2 ← obj.Ntfn.set_state st n s1 obj.NTFN_IDLE
      rustCompleteTail st arI s2 a t n) ⦃ r => r.2 = a ∧ ∃ σd σ',
        Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ2 = ({((), σd)}, False) ∧
        specUnblock t.bv σd = ({((), σ')}, False) ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.1 σ' ∧
        IFrame (L := L) Z.th s1 r.1 ∧ FinStep (st := st) Z.T Z.N Z.C Z.c s1 σ1 r.1 σ' ⦄ := by
    refine WP.spec_bind (P1.obj.Ntfn.set_state.val _ n obj.NTFN_IDLE) ?_
    rintro s2' rfl
    refine WP.spec_mono (completeTail_irelD J1.ip hmb s2 a σ2 hX2 ht hn hDon
      (fun σd hd => donShape_of I2 hkt2 hkn2 hnqT hsc1 hd)) ?_
    rintro r ⟨hra, σd, σ', hd, hu, hX', hSS', hTW'⟩
    exact ⟨hra, σd, σ', hd, hu, hX', hSS2.trans hSS', hTW2.trans hTW'⟩
  have ht0 : t ≠ 0#u64 := fun e => by
    obtain ⟨Q1, R1, hc1, -⟩ := J.xtop.fin.1.1.1.lists
    exact (hc1.tcbs t ht).ne0 (by rw [e]; rfl)
  have hmain : notification.complete_signal st arI s a n t ⦃ r => r.2 = a ∧ (P1.DonCore st (P1.Heap.tcbs H)
      (P1.Heap.scs H) n s1 → P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
        (P1.EH H) s1 r.1) ∧ ∃ σd σ',
        Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ2 = ({((), σd)}, False) ∧
        specUnblock t.bv σd = ({((), σ')}, False) ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.1 σ' ∧
        IFrame (L := L) Z.th s1 r.1 ∧ FinStep (st := st) Z.T Z.N Z.C Z.c s1 σ1 r.1 σ' ⦄ := by
    unfold notification.complete_signal
    step with P1.obj.Tcb.is_null.spec as ⟨bn, hbn'⟩
    simp only [hbn', ht0, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
    rintro v rfl
    rw [epState_eq, hst]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (obj.Ntfn.badge.spec s n) ?_
    rintro bb rfl
    refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE _) ?_
    rintro s1' rfl
    exact WP.spec_mono (WP.spec_and hfootT hirT) fun r ⟨hf, hra, hR⟩ => ⟨hra, hf, hR⟩
  -- `receive_ipc` is `complete_signal`
  have hxt := hI.1.toE.at_tcb ht hkt
  have hb1 : optRef (L.mem s (tBoundA t)) = some n.bv := hxt.bound.symm.trans hbn
  have hbz : L.mem s (tBoundA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb1; cases hb1
  have hbound : L.mem s (tBoundA t) = n := by
    rw [Notif.optRef_ne hbz] at hb1; exact P1.eq_of_bv (Option.some.inj hb1)
  refine WP.spec_mono (receive_ipc_preA (ar := arI) s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
    (by rw [← hbound]; exact hbz) hst (WP.spec_and hmain p1)) ?_
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
  have hspecC : Fl4Spec.completeSignal (Z := Unit) n.bv t.bv σ = specCompleteTail t.bv n.bv σ2 := by
    unfold Fl4Spec.completeSignal
    rw [nd_bind_one (getNotification_eq hk)]
    simp only [hact]
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt), nd_bind_one (setNotification_eq _ hk1)]
    rfl
  obtain ⟨xd, hkd⟩ := donate_tcb I2 hkt2 hkn2 hnqT hsc1 hd
  have hsT : specCompleteTail t.bv n.bv σ2 = specUnblock t.bv σd := by
    have e1 : specCompleteTail t.bv n.bv σ2 = specCompleteCheck t.bv n.bv σd := by
      unfold specCompleteTail; rw [nd_bind_one hd]; rfl
    rw [e1, specCompleteCheck_eqU (donShape_of I2 hkt2 hkn2 hnqT hsc1 hd) hkd]
  rw [receiveIpc_active b rights blk (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hke hk hact, hspecC, hsT, hu]
  exact ⟨_, Set.mem_singleton _, J'.xtop.relTop, _, _, _, _, _, _, J'⟩

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` with a null or free reply at a `MidN` state outside the
reply-push donation** (module docstring): `jRecvIpcUN` without
`¬ IpcActDon`. -/
theorem jRecvIpcUDN (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidN σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (Endp.rTcbA q) = 0#u64)
    (hPD : ¬ IpcPushDon σ p.bv rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  by_cases hAD : IpcActDon σ
  · obtain ⟨xt, n0, x, hkt, hbn, hkn, ⟨b0, hact⟩, -⟩ := hAD
    rw [hcur] at hkt
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ x hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    obtain ⟨xe, hke⟩ := hpE
    exact WP.spec_mono (J.recvIpcActDJN hAT hmb ht hcur hni hnq hkt hn hkn hbn hact true hke b sd true g gr hra
        b.bv (rightsOf sd true g gr))
      fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ => ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  · exact jRecvIpcUN hAT hmax htu J ht hcur hni hnq p b sd g gr rc rc' hpE hrc hHd hHr hun hAD hPD


set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` at `J` with a reply linked to another thread at a
`MidN` state outside the reply-push donation** (module docstring):
XTopJointRecvIpcLinkN's `jRecvIpcLinkN` without `¬ IpcActDon`, by `jRecvIpcUDN`. -/
theorem jRecvIpcLinkDN (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hni : MidN σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (q : U64) (g' : Bool) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x)) (hcr : CapRel (.Reply q g') rc')
    {xr : Fl4Spec.Reply} (hkr : σ.kheap q.bv = some (.reply xr))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : JHeld (L := L) Z.th s (.Reply q g')) (hi0 : L.mem s (Endp.rTcbA q) ≠ 0#u64)
    (hPD : ¬ IpcPushDon σ p.bv (.Reply q g')) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true (.Reply q g') ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hR := (J.xtop.irelK J.ks J.buf).1.toE
  obtain ⟨q0, hq, hqe⟩ := J.obj.reply _ xr hkr
  rw [Sched.bv_inj hqe] at hq
  have hrt : xr.replyTcb = some (L.mem s (Endp.rTcbA q)).bv := (hR.at_reply hq hkr).trans (Notif.optRef_ne hi0)
  obtain ⟨xi, hki, hsti⟩ := J.sv.replyTcb q.bv xr _ hkr hrt
  obtain ⟨i, hiT, hie⟩ := J.obj.tcb _ xi hki
  have hiq : L.mem s (Endp.rTcbA q) = i := (P1.eq_of_bv hie).symm
  rw [hiq] at hrt hki hi0
  have hict : i ≠ ct := by
    intro e
    subst e
    have hr := hni.run xi (by rw [hcur]; exact hki)
    rcases hsti with h | ⟨_, _, h⟩ <;> rw [h] at hr <;> simp [Fl4Spec.runnable] at hr
  have hne : σ.curThread ≠ i.bv := fun e => hict (P1.eq_of_bv (e.symm.trans hcur))
  refine receive_ipc_linked hiq hi0 hict ?_
  refine WP.spec_mono (J.cancelLinkJ hiT hki hsti) ?_
  rintro ⟨s1, a1⟩ ⟨hSS, h1, σ', he, hin, V, Ac', Lst', J'⟩
  dsimp only at h1 hSS J' ⊢
  subst h1
  have hm : ((), σ') ∈ (Fl4Spec.cancelIpc (Z := Unit) i.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have C : CancelLinkAt σ σ' i.bv q.bv xi := ⟨hki, hsti, hne, hm, hin⟩
  obtain ⟨hct', hid', hact', hrq', hkeep⟩ := cancelOther_keep hm hne
  have hR' := (J'.xtop.irelK J'.ks J'.buf).1.toE
  obtain ⟨xr', hkr', hrl⟩ := hR'.reply q hq
  have hnone : xr'.replyTcb = none := cancelOther_reply J.sv J'.sv hm hkr hrt hin hkr'
  have h0' : L.mem s1 (Endp.rTcbA q) = 0#u64 := optRef_none (hrl.symm.trans hnone)
  refine ⟨h0', ?_⟩
  have hcr' : rc' = absCap (.Reply q g') := hcr.abs
  subst hcr'
  have hsp : Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true
      (absCap (.Reply q g')) σ =
      Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true
      (absCap (.Reply q g')) σ' :=
    receiveIpc_linked _ _ _ _ hkr hrt (fun e => hne (hcur.trans e.symm)) he hkr' hnone
  rw [hsp]
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he', h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he'
  obtain ⟨xe', hke', -⟩ := hR'.ep p he'
  obtain ⟨x0, hk0, -⟩ := (J.xtop.irelK J.ks J.buf).1.tcb ct ht
  have hk0' : σ'.kheap ct.bv = some (.tcb x0) := hkeep ct.bv x0 (fun e => hict (P1.eq_of_bv e.symm)) hk0
  have hrun' : CurRun σ' := fun x hx => by
    rw [hct', hcur, hk0'] at hx
    simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx
    subst hx
    exact hni.run x0 (by rw [hcur]; exact hk0)
  have hN' : MidN σ' := ⟨by rw [hct', hid']; exact hni.1, hrun', by rw [hact']; exact hni.2.2.1,
    fun x hx => by
      rw [hct', hcur, hk0'] at hx
      simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx
      subst hx
      exact hni.2.2.2 x0 (by rw [hcur]; exact hk0)⟩
  exact jRecvIpcUDN (Z := Z.mv Z.G V) hAT hmax hmb htu J' ht (hct'.trans hcur) hN'
    (by rw [hct', hrq']; exact hnq) p b sd g gr (.Reply q g') _ ⟨xe', hke'⟩
    (Or.inr ⟨hcr, q, g', rfl, xr', hkr'⟩) (jHeld_of_same hSS hHd) (fun _ _ _ => jHeld_of_same hSS hHr)
    (Or.inr ⟨q, g', rfl, h0'⟩)
    (fun h => hPD (cancelLink_pushDon J J' C h))

end

end

end Fl4Proofs.P3
