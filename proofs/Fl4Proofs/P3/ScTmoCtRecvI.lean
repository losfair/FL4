/-
P3 (DESIGN.md §9), scheduling contexts: **the current thread's own
timeout-fault send to a receiver waiting on its timeout handler's endpoint,
the sender left `Inactive`** (KENTRY-PLAN kp17 (1)): XTopJointFaultTmo's
`JAtZ.sendTmoRecvIJ` (a scripted copy) for `t` the current thread, from the
state inside `charge_budget` (no `JAtZ` there).

* `ipcBufCapOK_tr`, `bufCover_tr`: the buffer facts across a kheap change
  keeping the TCBs' buffer fields and the frames.
* `cfr_congrK`, `ik_congrK`, `skeep_congrK`: the shadow frames read only the
  kheap and the scheduler fields other than the action.
* `JAtZ.sendTmoRecvCtIJ`: the copy, with the base `J0` a parameter
  (ScTmoCtBase's virtual base, related to the pre-state by kheap and `Sk`
  facts), `t = curThread` (so the receiver is not the current thread by
  `t ≠ d`), the action resume or choose (so no switch to `t`), and the end
  read on the shadow up to the action: the sender's `set_thread_state`
  leaves `ChooseNewThread` (`stsAct_cur`), which gives `ActIdle`, `CurRunM`
  and the `cur` disjunct directly.
-/
import Fl4Proofs.P3.ScTmoCtBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

theorem ipcBufCapOK_tr {σ σ' : State Unit} (h : Endp.IpcBufCapOK σ)
    (ht : ∀ p y, σ'.kheap p = some (.tcb y) → ∃ x, σ.kheap p = some (.tcb x) ∧
      x.tcbIpcframe = y.tcbIpcframe ∧ x.tcbIpcBuffer = y.tcbIpcBuffer)
    (ho : ∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = some (.archObj ao)) :
    Endp.IpcBufCapOK σ' := by
  intro t x' hx' dev p R mt vms md hf hR
  obtain ⟨x, hx, e1, e2⟩ := ht t x' hx'
  obtain ⟨h1, h2, h3, h4, h5⟩ := h t x hx dev p R mt vms md (by rw [e1]; exact hf) hR
  refine ⟨h1, h2, fun k hk' => ?_, by rw [← e2]; exact h4, h5⟩
  obtain ⟨sz, hsz⟩ := h3 k hk'
  rw [← e2]
  exact ⟨sz, ho _ _ hsz⟩

theorem bufCover_tr {T : Set U64} {B : Set (U64 × Word)} {σ σ' : State Unit} (h : Endp.BufCover T B σ)
    (ht : ∀ p y, σ'.kheap p = some (.tcb y) → ∃ x, σ.kheap p = some (.tcb x) ∧
      x.tcbIpcframe = y.tcbIpcframe ∧ x.tcbIpcBuffer = y.tcbIpcBuffer) :
    Endp.BufCover T B σ' := by
  intro u hu x' bb p hx' hp w hw
  obtain ⟨x, hx, e1, e2⟩ := ht u.bv x' hx'
  have hp' : Endp.ipcBufOf bb x = some p := by unfold Endp.ipcBufOf at hp ⊢; rw [e1, e2]; exact hp
  exact h u hu x bb p hx hp' w hw

theorem cfr_congrK {r t : ObjRef} {σ0 X X' : State Unit} (h : CFr r t σ0 X) (hk : X'.kheap = X.kheap)
    (hs : Sk X X') : CFr r t σ0 X' :=
  ⟨h.sk.trans hs, fun p => by rw [hk]; exact h.kh p⟩

theorem ik_congrK {t : ObjRef} {σ0 X X' : State Unit} (h : IK t σ0 X) (hk : X'.kheap = X.kheap)
    (hq : X'.readyQueues = X.readyQueues) (hs : Sk X X') : IK t σ0 X' :=
  ⟨fun p => by rw [hk]; exact h.1 p, hq.trans h.2.1, hs.rel.trans h.2.2.1, hs.tm.trans h.2.2.2⟩

theorem skeep_congrK {σ0 X X' : State Unit} (h : Ipc.SKeep σ0 X) (hk : X'.kheap = X.kheap) (hs : Sk X X') :
    Ipc.SKeep σ0 X' :=
  ⟨hs.rel.trans h.1, hs.tm.trans h.2.1, fun p y hy => h.2.2.1 p y (by rw [← hk]; exact hy),
    fun p y n hy => h.2.2.2 p y n (by rw [← hk]; exact hy)⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 64000000 in
/-- **The current thread's timeout-fault `send_ipc` to a waiting receiver,
the sender left `Inactive`** (module docstring): XTopJointFaultTmo's
`JAtZ.sendTmoRecvIJ` with `t` the current thread (Running/Restart at the send
`s7`, `σf`) and the base `J0` given (ScTmoCtBase's `JTH.tmoBaseCtJ`: the
thread `Inactive` with the fault, its SC's consumed time cleared, related to
the pre-state `σ` by `hk0`/`hk0t`/`hk0s`/`hsk0`); the sender's own
`set_thread_state` sets `ChooseNewThread` (`stsAct`), so the end is read on
the shadow up to the action (`cfr_congrK`). -/
theorem JAtZ.sendTmoRecvCtIJ {s0 : S} {σ0 : Fl4Spec.State Unit}
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a σ0)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {t : U64} (ht : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (htc : t.bv = σ.curThread)
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (b : U64)
    (hk0 : ∀ q, q ≠ t.bv → q ≠ sc.bv → σ0.kheap q = σ.kheap q)
    (hk0t : σ0.kheap t.bv = some (.tcb { x with tcbState := .inactive, tcbFault := some (.timeout b.bv) }))
    (hk0s : σ0.kheap sc.bv = some (.schedContext { y with scConsumed := (0#u64 : U64).bv } n))
    (hsk0 : Sk σ σ0) (hrq0 : σ0.readyQueues = σ.readyQueues)
    (hwB : P1.WritesIn st s s0 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hfB : P1.WritesIn st s s0 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s b ∨ False))
    {ts : Fl4Spec.ThreadState} (hrun : Fl4Spec.runnable ts = true) {s7 : S}
    (hI7 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s7
      (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) })))
    (hblk7 : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s7)
    (hW7 : P1.WritesIn st s s7 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hfoot7 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s7)
    (hcb7 : P1.CanBlock st (P1.Heap.tcbs H) Ac s7 t)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hke : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (badge : U64) (g gr : Bool)
    (hno : (g = false ∧ gr = false) ∨
      ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none) :
    endpoint.send_ipc st arI s7 a true false badge g gr false t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) true false badge.bv g gr false t.bv e.bv
        (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) }))).1,
        ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D r.1 r.2 z.2 ⦄ := by
  set xt : Fl4Spec.Tcb := { x with tcbState := ts, tcbFault := some (.timeout b.bv) } with hxt
  set σf := updK σ t.bv (.tcb xt) with hσf
  set xT : Fl4Spec.Tcb := { x with tcbState := .inactive, tcbFault := some (.timeout b.bv) } with hxT
  set yS : Fl4Spec.SchedContext := { y with scConsumed := (0#u64 : U64).bv } with hyS
  have hst : t.bv ≠ sc.bv := fun e0 => by rw [e0, hky] at hk; cases hk
  have hkf : ∀ q, q ≠ t.bv → σf.kheap q = σ.kheap q := fun q h1 => by simp [hσf, updK, h1]
  have hkfr : ∀ p, (rhoT σf t.bv sc.bv xT yS n).kheap p = σ0.kheap p := fun p => by
    by_cases h1 : p = t.bv
    · subst h1; rw [rhoT_kt hst, hk0t]
    · by_cases h2 : p = sc.bv
      · subst h2; rw [rhoT_ksc, hk0s]
      · rw [rhoT_kh h1 h2, hk0 p h1 h2, hkf p h1]
  have skf : Sk σ0 (rhoT σf t.bv sc.bv xT yS n) :=
    ⟨hsk0.ct.symm, hsk0.idle.symm, hsk0.cons.symm, hsk0.tm.symm, hsk0.csc.symm, hsk0.rel.symm, hsk0.cdt.symm,
      hsk0.orig.symm, hsk0.arch.symm, hsk0.dt.symm, hsk0.isc.symm⟩
  have Fr0 : CFr e.bv d.bv σ0 (rhoT σf t.bv sc.bv xT yS n) := ⟨skf, fun p => Or.inl (hkfr p)⟩
  have IK0 : IK d.bv σ0 (rhoT σf t.bv sc.bv xT yS n) :=
    ⟨fun p => by rw [hkfr p]; exact OIK.refl _ _, hrq0.symm, hsk0.rel.symm, hsk0.tm.symm⟩
  have SK0 : SKeep σ0 (rhoT σf t.bv sc.bv xT yS n) :=
    ⟨hsk0.rel.symm, hsk0.tm.symm, fun p y' hy => ⟨y', by rw [← hkfr]; exact hy, rfl⟩,
      fun p y' n' hy => by rw [← hkfr]; exact hy⟩
  have hP0 := J0.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hI := hI7
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J0.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J0.tcbs_eq.2
  have hte0 : t.bv ≠ e.bv := kheap_ne hk hke (fun _ h1 h2 => by subst h1; cases h2)
  have hse0 : sc.bv ≠ e.bv := kheap_ne hky hke (fun _ h1 h2 => by subst h1; cases h2)
  have hkx := hk
  have hk : σf.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))) := by rw [hkf _ (Ne.symm hte0)]; exact hke
  have hkt : σf.kheap t.bv = some (.tcb xt) := by simp [hσf, updK]
  have hrn : Fl4Spec.runnable xt.tcbState = true := hrun
  have hft : xt.tcbFault = some (.timeout b.bv) := rfl
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  obtain ⟨xd, hkd, -⟩ := hI.1.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s7 (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s7 (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := hte0
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdsc : d'.bv ≠ sc.bv := fun e0 => by
    have h1 : σf.kheap sc.bv = some (.schedContext y n) := by rw [hkf _ (Ne.symm hst)]; exact hky
    rw [e0, h1] at hkd; cases hkd
  have hkdσ : σ.kheap d'.bv = some (.tcb xd) := by rw [← hkf _ (Ne.symm htd')]; exact hkd
  have hkd0 : σ0.kheap d'.bv = some (.tcb xd) := by rw [hk0 _ (Ne.symm htd') hdsc]; exact hkdσ
  have hke0 : σ0.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := by
    rw [hk0 _ (Ne.symm hte0) (Ne.symm hse0)]; exact hke
  have hdc : d'.bv ≠ σf.curThread := fun h => htd' (htc.trans h.symm)
  -- P1's facts at the send
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := hblk7
  have hdH : d' ∈ P1.Heap.tcbs H := J0.zH.1 d' hdT
  have hHe : H e = some .ep := J0.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s7 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s7 (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s7 d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s7 e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s7 e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s7 e) ?_
  rintro _ rfl
  have hhead : (L.epQ s7 e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s7 σf hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s7 he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σf e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s7 s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s7 s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s7 s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, ea1, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hky1 : σ1.kheap sc.bv = some (.schedContext y n) := by
    simp [σ1, hse0, hσf, updK, Ne.symm hst, hky]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have hke0f : (rhoT σf t.bv sc.bv xT yS n).kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := by
    rw [hkfr]; exact hke0
  -- the shadow frame from the base
  have eρ1 : rhoT σ1 t.bv sc.bv xT yS n = updK (rhoT σf t.bv sc.bv xT yS n) e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    rw [hσ1, rhoT_updK _ (Ne.symm hte) (Ne.symm hse0)]
  have Fr1 : CFr e.bv d'.bv σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    refine Fr0.trans (CFr.upd hke0f ?_)
    exact (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
      by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
      by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    refine IK0.trans (IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hke0f ?_)
    exact (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : SKeep σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    refine SK0.trans ?_
    exact SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h)
      (fun _ _ h => by cases h)
  have htbk : ∀ p y', σf.kheap p = some (.tcb y') → ∃ x0, σ0.kheap p = some (.tcb x0) ∧
      x0.tcbIpcframe = y'.tcbIpcframe ∧ x0.tcbIpcBuffer = y'.tcbIpcBuffer := fun p y' hp => by
    by_cases h1 : p = t.bv
    · subst h1; rw [hkt] at hp; cases hp; exact ⟨_, hk0t, rfl, rfl⟩
    · have h2 : p ≠ sc.bv := fun e0 => by rw [e0, hkf _ (Ne.symm hst), hky] at hp; cases hp
      exact ⟨y', by rw [hk0 p h1 h2, ← hkf p h1]; exact hp, rfl, rfl⟩
  have hafw : ∀ p ao, σ0.kheap p = some (.archObj ao) → σf.kheap p = some (.archObj ao) := fun p ao hp => by
    have h1 : p ≠ t.bv := fun e0 => by rw [e0, hk0t] at hp; cases hp
    have h2 : p ≠ sc.bv := fun e0 => by rw [e0, hk0s] at hp; cases hp
    rw [hkf p h1, ← hk0 p h1 h2]; exact hp
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (ipcBufCapOK_tr J0.xferH.1 htbk hafw) (EpStep.ep hk)
  have hBC1 : Endp.BufCover Z.T Z.B σ1 := bufCover_epStep (bufCover_tr J0.xferH.2.1 htbk) (EpStep.ep hk)
  have hsc1 : sc ∈ P1.Heap.scs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J0.jpl
    exact ⟨_, (hJ.sc sc _ n (J0.c0 sc hsc) hk0s).2⟩
  -- the transfer
  refine WP.spec_bind (xferTmoStepJ hP0 (hH.epHyps hP0) hmax s1 a σ1 htu hR1 hS1 hOK1 hBC1 ht hdT htd hkt1 hkd1 hft
    hxsc hky1 e badge g hTP hdH h1 hB1 hX1 hS1' hSg1 hsc1) ?_
  rintro s2 ⟨x2, e2, hx2, hR2, hS2, hA2, w2, ea2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Ipc.tmoSt σ1 sc y n) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne htd', Function.update_of_ne hst]
    exact hkt1
  have hksc2 : σ2.kheap sc.bv = some (.schedContext yS n) := by
    rw [hσ2, updK_kheap, Function.update_of_ne (Ne.symm hdsc)]
    show Function.update σ1.kheap sc.bv _ sc.bv = _
    rw [Function.update_self]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc2 : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne (Ne.symm hde), Function.update_of_ne (Ne.symm hse0)]
    exact hk1e
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    have hns' : sc.bv ≠ e''.bv := by intro h; rw [← h, hksc2] at hz; cases hz
    rw [hσ2] at hz
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne (Ne.symm hne),
      Function.update_of_ne (Ne.symm hns')] at hz
    exact hq1 e'' he'' z hz
  have hrw : L.mem s2 (tReplyA d') = L.mem s7 (tReplyA d') := by
    rw [show tReplyA d' = core.num.U64.wrapping_add d' 3360#u64 from rfl, f2 d' hdH _ (by simp) (by simp) (by simp),
      ← show tReplyA d' = core.num.U64.wrapping_add d' 3360#u64 from rfl,
      hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
  have hscw8 : SW Z.C σf (scW sc 8#u64) := sw_hdr hI.2.2.1 hsc (K := 8#u64) (by simp) (by simp) (by decide)
  have hW2 : P1.WritesIn st s7 s2 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW1.trans1 (w2.mono fun b hb => by
    rcases hb with ⟨eb, -⟩ | (⟨y0, hy, K, h1', h2', -, eb⟩ | hb)
    · subst eb; exact Or.inl (Or.inl (Or.inr (Or.inr hscw8)))
    · have hyT : y0 ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inr ⟨y0, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩)
      rw [eb]; exact tfield_val (hP.tcb y0 hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _))
  have F2 : P1.WritesIn st s1 s2 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1) :=
    w2.mono fun b hb => by
      rcases hb with ⟨-, c0, hc0, hin⟩ | (⟨y0, hy, K, h1', h2', h3', eb⟩ | hb)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c0, hc0, hin⟩)))
      · exact Or.inl ⟨y0, hy, K, by omega, by omega, by omega, by omega, eb⟩
      · exact absurd hb (Set.notMem_empty _)
  have eρ2 : rhoT σ2 t.bv sc.bv xT yS n = updK (rhoT σ1 t.bv sc.bv xT yS n) d'.bv (.tcb x2) := by
    rw [hσ2, rhoT_updK _ (Ne.symm htd') hdsc, rhoT_updKsc _ hst]
  have hkd1ρ : (rhoT σ1 t.bv sc.bv xT yS n).kheap d'.bv = some (.tcb xd) := by
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd1
  have Fr2 : CFr e.bv d'.bv σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]
    exact Fr1.trans (CFr.upd hkd1ρ (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl,
      by rw [hx2], Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]; exact IK1.trans (IK.updSelf hkd1ρ hxsc2)
  have SK2 : SKeep σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]
    exact SK1.trans (SKeep.updK (p := d'.bv) (o := .tcb x2) (fun y h => ⟨xd, hkd1ρ, by cases h; exact hxsc2.symm⟩)
      (fun _ _ h => by cases h))
  have hks2 : L.ksb s2 = L.ksb s7 := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s7 (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3 X3,
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s3) σ3 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s3 σ3 ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ RbIn x3.tcbState ∧
      tsCode x3.tcbState ≠ 6 ∧ x3.tcbSchedContext = xd.tcbSchedContext ∧
      σ3.kheap sc.bv = some (.schedContext yS n) ∧
      (∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue) ∧
      P1.WritesIn st s7 s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) ∧
      P1.WritesIn st s7 s3 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) s7 b ∨ False) ∧
      CFr e.bv d'.bv σ0 (rhoT σ3 t.bv sc.bv xT yS n) ∧ IK d'.bv σ0 (rhoT σ3 t.bv sc.bv xT yS n) ∧
      SKeep σ0 (rhoT σ3 t.bv sc.bv xT yS n) ∧ σ3.curThread = σ.curThread ∧
      σ3.schedulerAction = σ.schedulerAction ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X3 s3 Q0 R0 ∧
      P1.BoundInv st (P1.Heap.tcbs H) Ac s3 ∧
      P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s3 ∧
      P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s3 ∧
      P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 ∧ P1.ExcT X3 d' ∧
      (d' ∈ X3 ∨ ¬ P1.Blocked (L.mem s3 (P1.stA d'))) ∧
      (∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d')) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h00 := optRef_none hrep
      simp only [h00, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hrA : L.mem s2 (P1.replyA d') = 0#u64 := by
        show L.mem s2 (tReplyA d') = 0#u64; rw [hrw]; exact h00
      exact ⟨σ2, x2, _, rfl, hR2, hS2, hkt2, hkd2, Or.inl ⟨_, _, _, hst2'⟩,
        by rw [hst2']; simp [tsCode], hxsc2, hksc2, hq2, hW2, footW_trans (footW_of F1) (F2.mono fun b hb => Or.inl hb),
        Fr2, IK2, SK2, rfl, rfl, h2, hB2, hX2, hS2'',
        hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl), hX2.noref0 hdta hrA⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s7 (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s7 (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hws : w.bv ≠ sc.bv := fun e0 => by
        have h1 : σf.kheap sc.bv = some (.schedContext y n) := by rw [hkf _ (Ne.symm hst)]; exact hky
        rw [e0, h1] at hkr; cases hkr
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := by
        rw [hσ2]
        simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne hwd, Function.update_of_ne hws]
        simp [σ1, hwe, hkr]
      have hkrσ : σ.kheap w.bv = some (.reply xr) := by rw [← hkf _ hwt]; exact hkr
      have hb' : xr.replyTcb = some d'.bv := hback_of J0.sv hkd0 e.bv w.bv dd xr (by rw [hstd, hrp]) (by rw [hk0 _ hwt hws]; exact hkrσ)
      have hX2' := IpcRel.ofSRN hR2 hS2
      have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
      rw [hrA] at hiR hit
      refine WP.spec_mono (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2
          hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
        (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
            (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
          (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
            (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
      rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩
      have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, hrA] at b2; rw [← b2]; exact z3
      set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
      have hkd3a : (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })).kheap d'.bv = some (.tcb (x2)) := by
        simp [Ne.symm hwd, hkd2]
      have hct3a : d'.bv ≠ (Notif.updK (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv
          (.tcb x3)).curThread := hdc
      have e3s : Notif.stsAct (Notif.updK (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv (.tcb x3))
          d'.bv = Notif.updK (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv (.tcb x3) :=
        stsAct_ne hct3a
      have hW3' : P1.WritesIn st s7 s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
        hW2.trans1 (hW3.mono fun b hb => cnW_back hks2 (SzKeepC.of (by
          intro p y0 m hp
          by_cases hps : p = sc.bv
          · subst hps; rw [hksc2] at hp; cases hp; exact ⟨y, by rw [hkf _ (Ne.symm hst)]; exact hky⟩
          · refine ⟨y0, ?_⟩
            rw [hσ2] at hp
            have hpd : p ≠ d'.bv := fun e0 => by rw [e0] at hp; simp at hp
            simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne hpd, Function.update_of_ne hps] at hp
            have hpe : p ≠ e.bv := fun e0 => by rw [e0] at hp; simp [σ1] at hp
            simpa [σ1, hpe] using hp)) hb)
      -- the shadows
      have hkr2ρ : (rhoT σ2 t.bv sc.bv xT yS n).kheap w.bv = some (.reply xr) := by
        rw [rhoT_kh hwt hws]; exact hkr2
      have hkd3aρ : (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply { xr with replyTcb := none })).kheap d'.bv =
          some (.tcb x2) := by
        simp only [updK_kheap, Function.update_of_ne (Ne.symm hwd)]
        rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd2
      have eρ3 : rhoT (Notif.stsAct (Notif.updK (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv
          (.tcb x3)) d'.bv) t.bv sc.bv xT yS n = Notif.stsAct (Notif.updK (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv
          (.reply { xr with replyTcb := none })) d'.bv (.tcb x3)) d'.bv := by
        rw [e3s, stsAct_ne (show d'.bv ≠ (Notif.updK (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv
          (.reply { xr with replyTcb := none })) d'.bv (.tcb x3)).curThread from hdc),
          rhoT_updK _ (Ne.symm htd') hdsc, rhoT_updK _ hwt hws]
      refine ⟨_, x3, _, e3, hR3, hS3, ?_, ?_, Or.inr rfl, by simp [x3, tsCode], by simp [x3, hxsc2], ?_, ?_, hW3',
        footW_trans (footW_trans (footW_of F1) (F2.mono fun b hb => Or.inl hb)) (footW_of fu3), ?_, ?_, ?_, ?_, ?_, h3,
        hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1),
        hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr, hS2''.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3']; exact P1.not_blocked_inactive),
        (hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr).noref hdta (by rw [e3']; exact P1.inactive_ne.1)
          (by rw [e3']; exact P1.inactive_ne.2)⟩
      · rw [stsAct_kheap]; simp [htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · rw [stsAct_kheap]; simp [Ne.symm hdsc, hws.symm, hksc2]
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [hwd] at hz
        exact hq2 e'' he'' z (by simpa [Ne.symm hne, Ne.symm hne'] using hz)
      · rw [eρ3]
        exact (Fr2.trans (CFr.upd hkr2ρ (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
          (CFr.stsIn hkd3aρ (Or.inl ⟨_, _, _, hst2'⟩))
      · rw [eρ3]
        have IK3a : IK d'.bv σ0 (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply { xr with replyTcb := none })) :=
          IK2.trans (IK.updOther (o' := .reply { xr with replyTcb := none }) hkr2ρ (fun o0 h => by
            rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
        exact (IK3a.trans (IK.updSelf (y := x3) hkd3aρ rfl)).trans (IK.sts _ _ _)
      · rw [eρ3]
        exact ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply { xr with replyTcb := none }) (fun y h => by cases h)
          (fun _ _ h => by cases h))).trans (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3aρ, by cases h; rfl⟩)
          (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
      · rw [e3s]; rfl
      · rw [e3s]; rfl
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
  rintro s3 ⟨σ3, x3, X3, hU, hR3, hS3, hkt3, hkd3, hrb3, hns3, hsc3, hksc3, hq3, hW3, F3, Fr3, IK3, SK3, hct3, hact3,
    h3, hB3, hX3, hS3', hSg3, hXc3, hx3, hnr3⟩
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = 5#u64 := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; exact hfr.1
  have hks3 : L.ksb s3 = L.ksb s7 := hW3.1
  -- the sender's `Inactive`
  have htH : t ∈ P1.Heap.tcbs H := J0.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := (IpcRel.ofSRN hR3 hS3).2.2.1
  have hna3 : L.actionW s3 ≠ t := actionW_ne_of hSR3 ht (by
    rw [hact3]; rcases hres with e0 | e0 <;> rw [e0] <;> intro e' <;> cases e')
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  have hstsT := WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 ht hkt3 hqt3
      (by have := runnable_code hrn; omega) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
      (set_thread_state_sfoot hSR3 ht sched.TS_INACTIVE))
    (WP.spec_and (P1.sts_all s3 t _ Q0 R0 h3 hB3 hX3 hS3' hSg3 htH P1.not_blocked_inactive P1.inactive_ne
        (Or.inr hnbt3) (hX3.noref (hTP t htH) hnrp3 (fun e0 => hnbt3 (Or.inr (Or.inl e0))))
        ⟨fun c hc' p hp hm => absurd hm (h0.notQ htH hcb7.nq hc' hp), fun c hc' hm => absurd hm (h0.notR htH hcb7.nr hc'),
          fun e0 => absurd e0 hna3⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s3 t sched.TS_INACTIVE h3 htH))
  -- FL4: no reply pushed, the sender `Inactive`
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧ sched.set_thread_state st s3 t sched.TS_INACTIVE = ok r.1)
    ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.NullFault; decide)]
    by_cases hi : (L.mem s7 (tReplyA d') != 0#u64) = true
    · rw [if_pos hi]
      have hgg : g = false ∧ gr = false := by
        rcases hno with h | hn
        · exact h
        · exfalso
          have hr0 := hn xd hkdσ _ _ _ hstd
          rw [hr0] at hrep
          have h00 := optRef_none hrep
          rw [h00] at hi
          simp at hi
      obtain ⟨rfl, rfl⟩ := hgg
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
    · rw [if_neg hi]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
  rintro ⟨s4, a4⟩ ⟨ha4, hs4⟩
  simp only at ha4 hs4
  subst ha4
  try dsimp only
  have hpost := hstsT
  rw [hs4] at hpost
  obtain ⟨⟨⟨hR4, hS4⟩, hW4⟩, ⟨h4, hB4, hX4, hS4', hSg4, -, k4⟩, fu4⟩ := (WP.spec_ok _).1 hpost
  have hkd4 : (ciSt σ3 t.bv xt).kheap d'.bv = some (.tcb x3) := by rw [ciSt_kh (Ne.symm htd')]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, (ciSt σ3 t.bv xt).kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z (by rw [← ciSt_kh (ciSt_ne hz (fun _ h => by cases h))]; exact hz)
  have hx4 : d' ∈ {y | y ∈ X3 ∧ y ≠ t} ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := by
    rcases hx3 with h | h
    · exact Or.inl ⟨h, Ne.symm htd⟩
    · right
      have e0 : L.mem s4 (P1.stA d') = L.mem s3 (P1.stA d') := by
        rw [P1.stA_eq]
        exact k4.fld d' hdH _ (by simp) (by simp) (by simp) (by simp) (fun e1 => absurd e1 (Ne.symm htd))
      rw [e0]; exact h
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' := fun r hr => by
    rcases k4.rtcb r hr with e0 | ⟨-, e0⟩
    · rw [e0]; exact hnr3 r hr
    · rw [e0]; intro h0'; exact hdta.ne0 (by rw [← h0']; rfl)
  have hks4 : L.ksb s4 = L.ksb s7 := hW4.1.trans hks3
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4 hns3
      .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q0 R0 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σ5 := Notif.stsAct (Notif.updK (ciSt σ3 t.bv xt) d'.bv (.tcb x5)) d'.bv with hσ5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 σ5 := IpcRel.ofSRN hR5 hS5
  have hW4' : P1.WritesIn st s7 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW3.trans1 (hW4.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3).1 hb))))
  have hW5' : P1.WritesIn st s7 s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q0, R0, h5.congrX (P1.excT_congr (X := {y | y ∈ X3 ∧ y ≠ t}) (fun y hy => hXc3 y hy.1))⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  -- the shadows to the end, and the end its own shadow
  have hdc4 : d'.bv ≠ (Notif.updK (ciSt σ3 t.bv xt) d'.bv (.tcb x5)).curThread := by
    show d'.bv ≠ (ciSt σ3 t.bv xt).curThread
    rw [(ciSt_skD (σ := σ3) (c := t.bv) (x := xt)).ct, hct3]; exact hdc
  have hdc4ρ : d'.bv ≠ (Notif.updK (rhoT σ3 t.bv sc.bv xT yS n) d'.bv (.tcb x5)).curThread := by
    show d'.bv ≠ σ3.curThread; rw [hct3]; exact hdc
  set Y5 := Notif.stsAct (Notif.updK (rhoT σ3 t.bv sc.bv xT yS n) d'.bv (.tcb x5)) d'.bv with hY5
  have hkd3ρ : (rhoT σ3 t.bv sc.bv xT yS n).kheap d'.bv = some (.tcb x3) := by
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd3
  have exT : ({ xt with tcbState := .inactive } : Fl4Spec.Tcb) = xT := by
    rfl
  have hk5t : σ5.kheap t.bv = some (.tcb xT) := by
    rw [hσ5, stsAct_kheap]; simp only [updK_kheap, Function.update_of_ne htd']; rw [ciSt_kc, exT]
  have hk5sc : σ5.kheap sc.bv = some (.schedContext yS n) := by
    rw [hσ5, stsAct_kheap]; simp only [updK_kheap, Function.update_of_ne (Ne.symm hdsc)]
    rw [ciSt_kh (Ne.symm hst)]; exact hksc3
  have hkY : σ5.kheap = Y5.kheap := by
    funext p
    rw [hσ5, hY5, stsAct_kheap, stsAct_kheap]
    by_cases h1 : p = d'.bv
    · subst h1; simp [updK]
    · simp only [updK_kheap, Function.update_of_ne h1]
      by_cases h2 : p = t.bv
      · subst h2; rw [ciSt_kc, exT, rhoT_kt hst]
      · by_cases h3 : p = sc.bv
        · subst h3; rw [ciSt_kh (Ne.symm hst), hksc3, rhoT_ksc]
        · rw [ciSt_kh h2, rhoT_kh h2 h3]
  have hsk5 : Sk Y5 σ5 := by
    rw [hσ5, hY5]; unfold ciSt Notif.stsAct
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hrq5 : σ5.readyQueues = Y5.readyQueues := by
    rw [hσ5, hY5]; unfold ciSt Notif.stsAct
    split_ifs <;> rfl
  have Fr5 : CFr e.bv d'.bv σ0 σ5 := cfr_congrK (Fr3.trans (CFr.stsRun hkd3ρ hrb3)) hkY hsk5
  have IK5 : IK d'.bv σ0 σ5 :=
    ik_congrK ((IK3.trans (IK.updSelf (y := x5) hkd3ρ rfl)).trans (IK.sts _ _ _)) hkY hrq5 hsk5
  have SK5 : SKeep σ0 σ5 :=
    skeep_congrK ((SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3ρ, by cases h; rfl⟩)
      (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)) hkY hsk5
  have hnqD : NotQueued σ0 d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x0, -, -, -, hkx0, -, hrx, -, -⟩ := J0.inv.rq dm p _ hm
      rw [hkd0] at hkx0; cases hkx0; rw [hstd] at hrx; cases hrx
    · obtain ⟨x0, -, -, -, hkx0, -, hrx, -, -⟩ := J0.inv.rel _ hm
      rw [hkd0] at hkx0; cases hkx0; rw [hstd] at hrx; cases hrx
  have hrib : RelIfBound σ5 d'.bv :=
    Ipc.RelIfBound.of_keep (J0.inv.rd d'.bv xd hkd0 (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σ5 := ((J0.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have hkX3 : (Notif.updK σ3 t.bv (.tcb { xt with tcbState := .inactive })).kheap t.bv =
      some (.tcb { xt with tcbState := .inactive }) := by simp [updK]
  have hsch3 : Fl4Spec.schedulable t.bv (Notif.updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) = false :=
    Bool.eq_false_iff.2 fun h => by
      obtain ⟨x', -, -, -, h1', -, h3', -⟩ := schedulable_inv h
      rw [hkX3] at h1'; cases h1'; simp [Fl4Spec.runnable] at h3'
  have act5 : σ5.schedulerAction = .chooseNewThread := by
    rw [hσ5, stsAct_ne hdc4]
    unfold ciSt
    have hc := Fl4Proofs.P3.Sched.stsAct_cur (σ := Notif.updK σ3 t.bv (.tcb { xt with tcbState := .inactive }))
      (t := t.bv) (by show t.bv = σ3.curThread; rw [hct3]; exact htc) hsch3
    have e1 : (Notif.updK σ3 t.bv (.tcb { xt with tcbState := .inactive })).schedulerAction = σ.schedulerAction :=
      hact3
    rcases stsAct_action (Notif.updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv with e0 | e0
    · exact e0
    · rcases hres with e' | e'
      · exact absurd (e0.trans (e1.trans e')) hc
      · exact e0.trans (e1.trans e')
  have hAI5 : ActIdle σ5 := ⟨fun u hu => (by rw [act5] at hu; cases hu), Fr5.idleOK J0.act.2⟩
  have hcur5 : σ5.schedulerAction = .chooseNewThread ∨ CurInv σ5 := Or.inl act5
  have hrun5 : CurRunM σ5 := Or.inl (by rw [act5]; intro e0; cases e0)
  -- the footprints from the base
  have hz7 : SzKeepC Z.C σ σf := SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := xt) (fun q hq => hkf q hq) hkt)
  have hWs5 : P1.WritesIn st s s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW7.trans1 (hW5'.mono fun b hb => cnW_back hW7.1 hz7 hb)
  have hz0 : SzKeepC Z.C σ0 σ := by
    intro p _ y0 m hp
    by_cases hps : p = sc
    · subst hps; rw [hky] at hp; cases hp; exact ⟨yS, hk0s⟩
    · have hps' : p.bv ≠ sc.bv := fun e0 => hps (P1.eq_of_bv e0)
      have hpt : p.bv ≠ t.bv := fun e0 => by rw [e0, hkx] at hp; cases hp
      exact ⟨y0, by rw [hk0 _ hpt hps']; exact hp⟩
  have hW05 : P1.WritesIn st s0 s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0) :=
    (writesIn_rebase hWs5 hwB (fun _ h => h)).mono fun b0 hb0 => CnW.back (s := s0) (s' := s) hwB.1.symm hz0 hb0
  have hfs5 := footW_trans (footW_of (W := fun _ => False) hfoot7) hfoot
  have hfoot05 : P1.WritesIn st s0 s5 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s0) :=
    (writesIn_rebase hfs5 hfB (fun _ h => h)).mono fun b0 hb0 => hb0.elim (P1.KW.ksb hfB.1.symm) False.elim
  have hI0 := J0.xtop.irelK J0.ks J0.buf
  have hF : IFrame (L := L) Z.th s0 s5 := IRel.iframe_of hI0 hW05 fun b0 hb0 => CnW.oobj hI0.2.2.1 hb0
  have htD := J0.not_dead_of_st hdT hkd0 (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, σ0.kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem s0 (rNextA q') = 0#u64 ∧ L.mem s0 (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D s0 _ σ0 J0 q' hq'' xr d'.bv xd hx'
      hxt' hkd0 (by rw [hstd]; rfl)
  obtain ⟨V', J5⟩ := J0.wake_postD (by rw [hsk0.arch]; exact hIR) hF hW05 hblk hfoot05 (DWFr.ofCFr Fr5) I5 (Fr5.bsa J0.bsa) hAI5
    hcur5 hrun5 hRR htD ⟨d', hdT, rfl⟩
  -- the tail
  have hk5 : σ5.kheap d'.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ σ5.releaseQueue := by rw [SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ5.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hy0 := SK5.2.2.2 p y n hy
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J0.inv.back _ _ _ hkd0 hp'
    rw [hy0] at hky'; cases hky'
    exact J0.bsa.tcb p y n d'.bv xd hy0 hyt hkd0 (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ5.idleThread := by
    rw [Fr5.sk.idle]
    intro h
    obtain ⟨x0, hkx0, -, hxs, -⟩ := J0.act.2
    rw [← h, hkd0] at hkx0; cases hkx0; rw [hstd] at hxs; cases hxs
  have htc5 : d'.bv ≠ σ5.curThread := by rw [Fr5.sk.ct, hsk0.ct]; exact hdc
  have hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none) := by
    rintro ⟨hg, hr⟩
    rcases hno with ⟨rfl, rfl⟩ | hn
    · rcases hg with h | h <;> cases h
    · exact hr (hn xd hkdσ _ _ _ hstd)
  have hspec := sendIpc_faultInactive_eq (don := false) hk hkd hde htd' hstd true badge.bv g gr hcond e2 hU hkt3 hkd3
    (by rw [hft]; simp) (t := t.bv)
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7', a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  refine ⟨((), σ7), ?_, V', Lst7, J7⟩
  rw [hspec]
  show ((), σ7) ∈ (Endp.specWakeTailE d'.bv σ5).1
  rw [h7]; exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
