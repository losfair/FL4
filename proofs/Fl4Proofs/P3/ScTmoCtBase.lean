/-
P3 (DESIGN.md §9), scheduling contexts: **the base `J` state of the
current thread's own timeout-fault send to a waiting receiver** (KENTRY-PLAN
kp17 (1)): XTopJointFaultTmo's `JAtZ.tmoBaseJ` for the current thread at the
state inside `charge_budget` (a `JTH` state, where no `JAtZ` holds).

The base is a virtual state: FL4's `set_fault` (four words), the current
thread's `set_thread_state INACTIVE` (its state word, the action word) and
the SC's `CONSUMED` word from the hole; the spec state `tmoCtSt`: the thread
`Inactive` with the fault (`stsAct`: a pending `ResumeCurThread` becomes
`ChooseNewThread`), its SC's consumed time cleared. `JAtZ` there is assembled
from the hole's base `JAtZ` (as ScChargeTA's `JTH.tmoBlockJA`) with the
composite frame `ScOnly` (the head), `BFrT` and `KFr` (the thread's TCB, via
a blocked-on-send intermediate: both frames' lemma suites apply), then the
SC step (`ScOnly`/`QKY`); `Inv` by `InvBut.ik` at the hole (an `Inactive`
thread is not `inClassR`).

The real send (`ScTmoCtRecv`) reads its frame from this base on the shadows
`rhoT` (the thread's TCB and SC as here); the action differs from the
shadow's only before the thread's own `set_thread_state`, and the frames
(`CFr`, `IK`, `SKeep`) do not read the action.
-/
import Fl4Proofs.P3.ScChargeTA
import Fl4Proofs.P3.XTopJointFaultTmo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec

theorem updK_updK_same (σ : State Unit) (p : ObjRef) (o o' : KernelObject) :
    Notif.updK (Notif.updK σ p o) p o' = Notif.updK σ p o' := by
  simp only [Notif.updK, Function.update_idem]

/-- `ScOnly` followed by an SC update at `c` keeping the fields `ScChgO`
reads. -/
theorem ScOnly.updC {c : ObjRef} {σ0 σ : State Unit} (h : ScOnly c σ0 σ) {y : SchedContext} {n : Nat}
    (hky : σ.kheap c = some (.schedContext y n)) (v : Word) :
    ScOnly c σ0 (Notif.updK σ c (.schedContext { y with scConsumed := v } n)) := by
  intro p
  by_cases hp : p = c
  · subst hp
    right
    rcases h p with e | ⟨o, o', h1, h2, -, y0, z, m, e1, e2, k1, k2, k3, k4, k5⟩
    · exact ⟨_, _, by rw [← e]; exact hky, by simp [Notif.updK], rfl, y, { y with scConsumed := v }, n, rfl, rfl, rfl, rfl, rfl, rfl,
        Or.inl rfl⟩
    · rw [hky, e2] at h2
      cases h2
      exact ⟨_, _, h1, by simp [Notif.updK], rfl, y0, { y with scConsumed := v }, _, e1, rfl, k1, k2, k3, k4, k5⟩
  · have e : (Notif.updK σ c (.schedContext { y with scConsumed := v } n)).kheap p = σ.kheap p := by
      simp [Notif.updK, hp]
    rw [e]; exact h p

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

/-- **The spec's base state** (module docstring): the thread `t` given the
timeout fault and made `Inactive` (`set_thread_state`'s action step), then
its SC's consumed time cleared. -/
def tmoCtSt (σ : Fl4Spec.State Unit) (t sc : U64) (x : Fl4Spec.Tcb) (y : Fl4Spec.SchedContext) (n : Nat)
    (b : U64) : Fl4Spec.State Unit :=
  Ipc.tmoSt (stsAct (updK (updK σ t.bv (.tcb { x with tcbFault := some (.timeout b.bv) })) t.bv
    (.tcb { x with tcbState := .inactive, tcbFault := some (.timeout b.bv) })) t.bv) sc y n

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 64000000 in
/-- **The base `J` state of the current thread's timeout-fault send**
(module docstring). -/
theorem JTH.tmoBaseCtJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hj : JTH (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {t : U64} (ht : t ∈ Z.T)
    (htc : t.bv = σ.curThread) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrr : x.tcbState = .running ∨ x.tcbState = .restart)
    {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv) (hscc : sc.bv = σ.curSc)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : NotQueued σ t.bv) (hidt : σ.idleThread ≠ t.bv) (b : U64) :
    ∃ sB : S, P1.WritesIn st s sB (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) ∧
      P1.WritesIn st s sB (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) s b ∨ False) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D sB a (tmoCtSt σ t sc x y n b) := by
  have J := Hj.j0
  have hO := Hj.ksc
  have hP0 := J.ip
  have hP := hP0.e
  have hks0 : L.ksb s = L.ksb s0 := Hj.ws.1
  have hI0 := J.xtop.irelK J.ks J.buf
  have hI' := Hj.xtop.irelK (by rw [hks0]; exact J.ks) Hj.buf
  have hI : IRel st Z.th σ0.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := by
    rw [← Hj.arch]; exact hI'
  have hS := Hj.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP.tcb
  have hta := hP.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP.tcb
  have hk0 : σ0.kheap t.bv = some (.tcb x) := hO.tcbB hk
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ0.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hst : sc.bv ≠ t.bv := fun e => by rw [e, hk] at hky; cases hky
  have hD : t ∉ D := fun h => by
    have hd := J.jcov.dead t h
    have h1 := (hd.1 htH).1
    obtain ⟨x1, hk1, hTR⟩ := hI0.1.tcb t ht
    rw [hk0] at hk1; cases hk1
    have hst' := hTR.st
    rw [← stA_tStA, h1] at hst'
    unfold sched.TS_INACTIVE at hst'
    rcases hrr with e | e <;> rw [e] at hst' <;> simp [tsCode] at hst'
  have hsc1 : sc ∈ P1.Heap.scs H := by
    obtain ⟨y0, hy0, -⟩ := hO.scB hky
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨_, (hJ.sc sc y0 n (J.c0 sc hsc) hy0).2⟩
  -- the FL4 step from the base to the hole
  have hC1 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0 s σ :=
    ⟨Hj.ws.mono fun b hb => Or.inl (Or.inl hb), SzKeepC.of hO.szKeep⟩
  -- `set_fault`
  obtain ⟨s7, -, ⟨⟨-, hI7⟩, hs7⟩, ⟨hblk7, -, hcb7⟩, hfoot7⟩ := spec_exists (WP.spec_and (WP.spec_and
    (set_fault_timeout_top hP0 hI ht hk b) (set_fault_timeout_eq s t b))
    (WP.spec_and (P1.faults.set_fault.blk (U := ∅) s t (error.Fault.Timeout b)
      (t0 := t) Hj.blk htH (fun _ h => by simp at h) (by
        obtain ⟨Q, R0, hcq, hs⟩ := hS.lists
        obtain ⟨x7, hk7, hTR7⟩ := hI.1.tcb t ht
        rw [hk] at hk7; cases hk7
        have hv7 : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR7.st
        have hrr' : L.mem s (P1.stA t) = sched.TS_RUNNING ∨ L.mem s (P1.stA t) = sched.TS_RESTART := by
          rcases hrr with e | e
          · left; apply UScalar.eq_of_val_eq; rw [P1.stA_eq, ← tStA_eq, hv7, e]; unfold sched.TS_RUNNING; rfl
          · right; apply UScalar.eq_of_val_eq; rw [P1.stA_eq, ← tStA_eq, hv7, e]; unfold sched.TS_RESTART; rfl
        obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs.tcb t ht
        rw [hk] at hkt6; cases hkt6
        have hst6 : L.mem s (scA t) = sc := P1.eq_of_bv (Notif.optRef_some (hsct6.symm.trans hxsc)).2
        obtain ⟨y', n', hky', hy'⟩ := hs.scs sc hsc
        rw [hky] at hky'; cases hky'
        have hmx : (L.rmax s (L.mem s (scA t))).val ≠ 0 := by rw [hst6]; exact hy'.rmax_ne hya
        refine ⟨htH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rcases hrr' with h | h <;> rw [h]
          · exact P1.not_blocked_running
          · exact P1.not_blocked_restart
        · rcases hrr' with h | h <;> rw [h]
          · exact P1.running_ne.1
          · exact P1.restart_ne.1
        · by_contra hq'
          have hm := (hcq.queued t ht).1 hq'
          exact hnq.1 0 _ (by rw [hs.rq _ (hcq.prio t ht), mem_map_bv]; exact hm)
        · by_contra hq'
          have hm := (hcq.released t ht).1 hq'
          exact hnq.2 (by rw [hs.rel, mem_map_bv]; exact hm)
        · exact actionW_ne_of hS ht (by rcases hres with e | e <;> rw [e] <;> intro e' <;> cases e')
        · intro h
          have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
            unfold P1.LawfulStore.idleW nodeW; rw [hcq.cur]
          exact hidt (by rw [hs.idleTh, ← ei, h])
        · intro hbd
          obtain ⟨⟨Q', R', h0⟩, hBd, hXi, hSc, hSg⟩ := Hj.blk
          obtain ⟨hiS, -, -⟩ := hXi.2.2.bound _ htH hbd
          exact (hSc.act _ hiS).2 (fun e => hmx (by rw [e]; rfl))))
      (P1.faults.set_fault.kw (Cs := Cs) (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s t (error.Fault.Timeout b) hTH htH)))
  set xF : Fl4Spec.Tcb := { x with tcbFault := some (.timeout b.bv) } with hxF
  set σF := updK σ t.bv (.tcb xF) with hσF
  have hkF : σF.kheap t.bv = some (.tcb xF) := by simp [hσF, updK]
  have hkFp : ∀ q, q ≠ t.bv → σF.kheap q = σ.kheap q := by
    intro q hq'; rw [hσF]; simp only [updK, Function.update_of_ne hq']
  have hC2 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ s7 σF := by
    refine ⟨?_, SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := xF) (fun q hq' => by simp [hσF, updK, hq']) hkF)⟩
    subst hs7
    have w := (((writesIn_wr (st := st) (s := s) (v := fl4_abi.consts.fault.Timeout) (a_fault hta).1).trans
      (writesIn_wr (v := b) (a_fw0 hta).1)).trans (writesIn_wr (v := 0#u64) (a_fw1 hta).1)).trans
      (writesIn_wr (v := 0#u64) (a_fw2 hta).1)
    refine w.mono fun w0 hw0 => ?_
    have k : ∃ K : Nat, 256 ≤ K ∧ K < 4096 ∧ K ≠ 3440 ∧ K ≠ 3472 ∧ (K ≠ 3512 ∧ K ≠ 3664) ∧ w0.val = t.val + K := by
      rcases hw0 with ((h | h) | h) | h <;> subst h
      · exact ⟨3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩
      · exact ⟨3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩
      · exact ⟨3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩
      · exact ⟨3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩
    obtain ⟨K, k1, k2, k3, k4, k5, k6⟩ := k
    exact Or.inl (Or.inr ⟨t, ht, K, k1, k2, k3, k4, k5, k6⟩)
  -- `set_thread_state t INACTIVE`
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := hblk7
  have hrn : Fl4Spec.runnable xF.tcbState = true := by
    show Fl4Spec.runnable x.tcbState = true
    rcases hrr with e | e <;> rw [e] <;> rfl
  have hnb : tsCode xF.tcbState ≠ 3 ∧ tsCode xF.tcbState ≠ 4 := by have := runnable_code hrn; omega
  have hSR7 : SchedRel st Z.N Z.T Z.C Z.c s7 σF := hI7.2.2.1
  have hxt7 := hI7.1.toE.at_tcb ht hkF
  have hw7 : (L.mem s7 (P1.stA t)).val = tsCode xF.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt7.st]
  obtain ⟨hnbt7, hnrp7⟩ := P1.run_word (w := L.mem s7 (P1.stA t)) (by rw [hw7]; exact runnable_code hrn)
  have hna7 : L.actionW s7 ≠ t := actionW_ne_of hSR7 ht (by
    show σ.schedulerAction ≠ _
    rcases hres with e | e <;> rw [e] <;> intro e' <;> cases e')
  have hqt7 := Endp.not_queued hI7.1.toE ht hkF hnb
  obtain ⟨s8, -, ⟨⟨⟨hR8, hS8⟩, hW8⟩, ⟨h8, hB8, hX8, hS8', hSg8, -, -⟩, fu8⟩⟩ := spec_exists
    (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s7 σF hI7.1.toE (IpcRel.toSRN hI7.1 hI7.2) ht hkF hqt7
      (by have := runnable_code hrn; omega) .inactive (by simp [tsCode]) sched.TS_INACTIVE
      (by unfold sched.TS_INACTIVE; rfl))
      (set_thread_state_sfoot hSR7 ht sched.TS_INACTIVE))
    (WP.spec_and (P1.sts_all s7 t _ Q0 R0 h0 hB0 hX0 hS0 hSg0 htH P1.not_blocked_inactive P1.inactive_ne
        (Or.inr hnbt7) (hX0.noref (hTH t htH) hnrp7 (fun e0 => hnbt7 (Or.inr (Or.inl e0))))
        ⟨fun c hc' p hp hm => absurd hm (h0.notQ htH hcb7.nq hc' hp), fun c hc' hm => absurd hm (h0.notR htH hcb7.nr hc'),
          fun e0 => absurd e0 hna7⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s7 t sched.TS_INACTIVE h0 htH)))
  set xT : Fl4Spec.Tcb := { x with tcbState := .inactive, tcbFault := some (.timeout b.bv) } with hxT
  set σT := stsAct (updK σF t.bv (.tcb xT)) t.bv with hσT
  have hI8 : IRel st Z.th σ0.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s8 σT := IpcRel.ofSRN hR8 hS8
  have hblk8 : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s8 :=
    ⟨⟨Q0, R0, h8.congrX P1.empty_congr⟩,
      hB8, hX8, hS8', hSg8⟩
  have hkT : σT.kheap t.bv = some (.tcb xT) := by rw [hσT, stsAct_kheap]; simp [updK]
  have hkTp : ∀ q, q ≠ t.bv → σT.kheap q = σ.kheap q := by
    intro q hq'; rw [hσT, stsAct_kheap]; simp only [updK, Function.update_of_ne hq']; exact hkFp q hq'
  have hkyT : σT.kheap sc.bv = some (.schedContext y n) := by rw [hkTp _ hst]; exact hky
  have hC3 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σF s8 σT :=
    ⟨hW8.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot hb)),
      SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := xT) (fun q hq' => by rw [hkTp q hq', hkFp q hq']) hkT)⟩
  -- the SC's consumed time
  obtain ⟨⟨cv, sB⟩, -, ⟨hsB, -, -, hIB⟩, hblkB, fuB, -⟩ := spec_exists (WP.spec_and
    (update_consumed_irel (ar := arI) hP0 s8 a σT hI8 hsc hkyT hmax htu)
    (P1.schedcontext.update_consumed.blk hAT s8 a sc hblk8 hsc1))
  simp only at hsB hIB hblkB fuB
  set yS : Fl4Spec.SchedContext := { y with scConsumed := (0#u64 : U64).bv } with hyS
  set σB := tmoCtSt σ t sc x y n b with hσB
  have eB : updSc σT sc.bv yS n = σB := rfl
  rw [eB] at hIB
  have hkB : σB.kheap sc.bv = some (.schedContext yS n) := by
    rw [← eB]; simp only [updSc, Notif.updK, Function.update_self]
  have hkBt : σB.kheap t.bv = some (.tcb xT) := by
    rw [← eB]; simp only [updSc, updK]; rw [Function.update_of_ne (Ne.symm hst)]; exact hkT
  have hkBp : ∀ q, q ≠ t.bv → q ≠ sc.bv → σB.kheap q = σ.kheap q := by
    intro q h1 h2; rw [← eB]; simp only [updSc, updK]; rw [Function.update_of_ne h2]; exact hkTp q h1
  obtain ⟨Qs, Rs, hcs, hsps⟩ := hS.lists
  obtain ⟨ys, ns, hkys, hys⟩ := hsps.scs sc hsc
  rw [hky] at hkys; cases hkys
  have hal8 : P1.Aligned (scW sc 8#u64) := (hys.hdr (K := 8#u64) (by simp) (by simp)).1
  have hC4 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s8 σT sB σB := by
    refine ⟨?_, SzKeepC.of (SzKeep.of_sc (p := sc.bv) (fun q hq => by rw [← eB]; simp [updSc, updK, hq]) hkyT hkB)⟩
    rw [hsB]
    exact (writesIn_wr hal8).mono fun b hb => Or.inl (Or.inl (Or.inr (Or.inr
      (hb ▸ sw_hdr hI8.2.2.1 hsc (K := 8#u64) (by simp) (by simp) (by decide)))))
  -- the footprints
  have hWs : P1.WritesIn st s sB (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    ((hC2.trans hC3).trans hC4).1
  have hW : P1.WritesIn st s0 sB (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0) :=
    (((hC1.trans hC2).trans hC3).trans hC4).1
  have hfoot : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s sB :=
    P1.Foot.trans (P1.Foot.trans hfoot7 fu8) (P1.Foot.mono fuB (Set.empty_subset _))
  refine ⟨sB, hWs, footW_of hfoot, ?_⟩
  -- the spec frames: the hole, a blocked-on-send intermediate, `Inactive`, the SC
  set xM : Fl4Spec.Tcb := { x with tcbState := .blockedOnSend t.bv default, tcbFault := some (.timeout b.bv) }
    with hxM
  set σM := updK σ t.bv (.tcb xM) with hσM
  have hkM : σM.kheap t.bv = some (.tcb xM) := by simp [hσM, updK]
  have F1 : BFrT t.bv t.bv σ σM := by
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun q => ?_⟩
    by_cases hqt : q = t.bv
    · subst hqt
      exact Or.inr ⟨_, _, hk, hkM, Or.inl ⟨x, t.bv, default, some (.timeout b.bv), rfl, rfl, rfl⟩⟩
    · exact Or.inl (by simp [hσM, updK, hqt])
  have eK : stsAct (updK σM t.bv (.tcb xT)) t.bv = σT := by
    rw [hσT, hσM, hσF, updK_updK_same, updK_updK_same]
  have F2 : KFr t.bv σM σT := by
    rw [← eK]
    exact (KFr.upd hkM (Or.inl ⟨xM, .inactive, some (.timeout b.bv), rfl, rfl, rfl,
      Or.inl ⟨t.bv, default, rfl⟩, Or.inl rfl⟩)).trans (KFr.sts _ _ _)
  have F3 : ScOnly sc.bv σT σB := by
    rw [← eB]; exact ScOnly.updC (fun _ => Or.inl rfl) hkyT _
  have F3q : QKY σT σB := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
    by_cases hq : q = sc.bv
    · subst hq; exact Or.inr (Or.inr ⟨y, yS, n, hkyT, hkB, rfl⟩)
    · exact Or.inl (by rw [← eB]; simp [updSc, updK, hq])
  have hscc0 : sc.bv = σ0.curSc := hscc.trans Hj.csc
  -- the scheduler fields
  have skT : Sk σ σT := F1.sk.trans F2.sk
  have e_ct : σB.curThread = σ0.curThread := skT.ct.trans Hj.ct
  have e_idle : σB.idleThread = σ0.idleThread := skT.idle.trans Hj.idle
  have e_csc : σB.curSc = σ0.curSc := skT.csc.trans Hj.csc
  have e_cdt : σB.cdt = σ0.cdt := skT.cdt.trans Hj.cdt
  have e_orig : σB.isOriginalCap = σ0.isOriginalCap := skT.orig.trans Hj.orig
  have e_arch : σB.archState = σ0.archState := skT.arch.trans Hj.arch
  have e_isc : σB.idleSc = σ0.idleSc := skT.isc.trans Hj.isc
  have e_cons : σB.consumedTime = 0 := skT.cons.trans Hj.cons
  have hkX : (updK σF t.bv (.tcb xT)).kheap t.bv = some (.tcb xT) := by simp [updK]
  have hschT : Fl4Spec.schedulable t.bv (updK σF t.bv (.tcb xT)) = false := Bool.eq_false_iff.2 fun h => by
    obtain ⟨x', -, -, -, h1', -, h3', -⟩ := schedulable_inv h
    rw [hkX] at h1'; cases h1'; simp [hxT, Fl4Spec.runnable] at h3'
  have hactT : σT.schedulerAction = .chooseNewThread := by
    have hc := Fl4Proofs.P3.Sched.stsAct_cur (σ := updK σF t.bv (.tcb xT)) (t := t.bv) htc hschT
    rcases stsAct_action (updK σF t.bv (.tcb xT)) t.bv with e | e
    · exact e
    · rcases hres with e' | e'
      · exact absurd (e.trans e') hc
      · exact e.trans e'
  have hact3 : σB.schedulerAction = .chooseNewThread := hactT
  -- composite frame facts from the base
  have hszc : SzKeep σ0 σB := SzKeep.trans' (SzKeep.trans' (SzKeep.trans' hO.szKeep F1.szKeep) F2.szKeep) F3.szKeep
  have hykc : YKeep σ0 σB := ((hO.ykeep.trans F1.ykeep).trans F2.ykeep).trans F3.ykeep
  have hmkc : McpKeep σ0 σB := ((hO.mcpKeep.trans F1.mcpKeep).trans F2.mcpKeep).trans F3.mcpKeep
  have hbkc : BufKeep σ0 σB :=
    BufKeep.trans (BufKeep.trans (BufKeep.trans hO.bufKeep F1.bufKeep) F2.bufKeep) F3.bufKeep
  have hkbc : KBack σ0 σB := KBack.trans' (KBack.trans' (KBack.trans' hO.kback F1.kback) F2.kback) F3.kback
  have hkszc : KSz σ0 σB := KSz.trans (KSz.trans (KSz.trans hO.ksz F1.ksz) F2.ksz) F3.ksz
  have hksubc : KSub σ0 σB := KSub.trans (KSub.trans (KSub.trans hO.ksub F1.ksub) F2.ksub) F3.ksub
  have hrbc : KhRB σ0 σB := KhRB.trans (KhRB.trans (KhRB.trans hO.khrb F1.khrb) F2.khrb) F3.khrb
  have hfkc : IpcFrKeep σ0 σB := ((hO.ipcFr.trans F1.ipcFr).trans F2.ipcFr).trans F3.ipcFr
  -- forward facts for other objects
  have hfw : ∀ q o, σ0.kheap q = some o → q ≠ t.bv → (∀ y n, o ≠ .schedContext y n) → σB.kheap q = some o :=
    fun q o hq hqt hn => by
      have hqs : q ≠ sc.bv := fun e => by
        subst e
        obtain ⟨y0, hy0, -⟩ := hO.scB hky
        rw [hy0] at hq; cases hq; exact hn _ _ rfl
      rw [hkBp q hqt hqs]; exact hO.othF hq hn
  have hbw : ∀ q o, σB.kheap q = some o → q ≠ t.bv → (∀ y n, o ≠ .schedContext y n) → σ0.kheap q = some o :=
    fun q o hq hqt hn => by
      have hqs : q ≠ sc.bv := fun e => by subst e; rw [hkB] at hq; cases hq; exact hn _ _ rfl
      rw [hkBp q hqt hqs] at hq; exact hO.othB hq hn
  have haoc : ∀ q ao, σ0.kheap q = some (.archObj ao) → σB.kheap q = some (.archObj ao) := fun q ao h =>
    hfw q _ h (fun e => by rw [e, hk0] at h; cases h) (fun _ _ e => by cases e)
  have ck1 : ∀ q y n, σ0.kheap q = some (.schedContext y n) → ∃ y', σB.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies := fun q y n hq => by
    obtain ⟨z, hz, -, -, -, hr, -⟩ := hO.scF hq
    obtain ⟨z', hz', -, -, -, hr', -⟩ := F3.scF (F2.scF (F1.scF hz))
    exact ⟨z', hz', hr'.trans hr⟩
  have ck2 : ∀ q x, σ0.kheap q = some (.reply x) → ∃ x', σB.kheap q = some (.reply x') ∧ x'.replySc = x.replySc :=
    fun q x hq => ⟨x, hfw q _ hq (fun e => by rw [e, hk0] at hq; cases hq) (fun _ _ e => by cases e), rfl⟩
  -- the assembly (as `JTH.tmoBlockJA`)
  have hAR' : AR a σ0.archState.x64CurrentCr3 := by
    have h := Hj.xtop.fin.1.1.2.2.2.2.2.2; rw [Hj.arch] at h; exact h
  have hF : IFrame (L := L) Z.th s0 sB := IRel.iframe_of hI0 hW fun b hb => CnW.oobj hI0.2.2.1 hb
  have hIR' : IRel st Z.th σ0.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c sB σB := hIB
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR' hAR' hF.1 e_cdt e_orig hksubc hF.2
  have hks : L.ksb sB = L.ksb s0 := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hW
  have hCR' : CallRel (L.mem sB) Z.R Z.C σB Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck1 _ y n hy) (fun d _ x hx => ck2 _ x hx)
  have hRP' := J.rp.frame hks hszc
  have hRF' : RFree (L.mem sB) Z.R Z.C σB Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, hbw _ _ hy (fun e => by rw [e, hkBt] at hy; cases hy)
      (fun _ _ e => by cases e), hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have eN : L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb hks0 _ _
  have hDbg : L.mem sB (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [← Hj.dbg]
    exact hfoot.mem_eq J.kern.dwAl fun hk => P1.dbg0_not_schedW Hj.blk J.kern.cs0 (Or.inl (by rw [eN]; exact hk))
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c sB σB := hIR'.2.2.1
  have hidT : IdleOK σT := KFr.idleOK F2 (F1.idleOK Hj.act.2 hidt)
  have hAIT : ActIdle σT := ⟨fun u hu => (by rw [hactT] at hu; cases hu), hidT⟩
  have hAI3 : ActIdle σB := F3q.actIdle hAIT
  have hrun3 : CurRunM σB := Or.inl (by rw [hact3]; intro e; cases e)
  -- the dead are kept (the thread is not dead)
  have hdead : ∀ q ∈ D, DeadP (L := L) H sB q := fun q hq => by
    have hd := J.jcov.dead q hq
    have hqt : q.bv ≠ t.bv := fun h => hD (by rw [← P1.eq_of_bv h]; exact hq)
    refine J.deadP_keep hS3 hIR'.1
      (fun x hx h0 => ⟨_, hfw _ _ hx hqt (fun _ _ e => by cases e), rfl, rfl, Or.inl rfl⟩)
      (fun x hx => hfw _ _ hx hqt (fun _ _ e => by cases e))
      (fun x hx => ⟨x, hfw _ _ hx hqt (fun _ _ e => by cases e), Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, hfw _ _ hx hqt (fun _ _ e => by cases e), rfl⟩)
      (fun x n hx => by
        obtain ⟨z, hz, k1', -, -, -, k5'⟩ := hO.scF hx
        obtain ⟨z', hz', k1'', -, -, -, k5''⟩ := F3.scF (F2.scF (F1.scF hz))
        exact ⟨z', hz', Or.inl (k1''.trans k1'), by
          rcases k5'' with e | e
          · rw [e]; exact k5'
          · exact Or.inr e⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) e_idle hAI3.1
      (J.yld.frame k2 hykc) (hykc.dk q.bv) hd
  have hidl := J.idleW_keep hS3 e_idle e_isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq sB σB := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hszc q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 e_ct e_csc (fun sl h => Or.inl (by rw [← e_orig]; exact h))
    (by rw [e_arch]) haoc hDbg (D' := D)
  have hRR' := J.rrecv.frame k4 hrbc
  have hjcov : JCovD (L := L) Z.th H Z.G D Cs sB := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    exact J.jcov.same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩)
      (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik` at the hole; the thread `Inactive`, not `inClassR`)
  have hik : IK t.bv σ σB := by
    have i1 : IK t.bv σ σF := IK.updSelf hk rfl
    have i2 : IK t.bv σF σT := (IK.updSelf (y := xT) hkF rfl).trans (IK.sts _ _ _)
    have i3 : IK t.bv σT σB := by
      have hob : Fl4Proofs.P3.Sched.IKObj (sc.bv ≠ t.bv) (.schedContext y n) (.schedContext yS n) := by
        unfold Fl4Proofs.P3.Sched.IKObj
        refine ⟨fun x0 e0 => ?_, fun y' n' e0 => ?_, fun x0 e0 => ?_, fun x0 e0 => ?_, fun y' n' _ => ⟨y, n, rfl⟩,
          fun x0 e0 => ?_⟩
        · cases e0
        · cases e0; exact ⟨yS, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · cases e0
        · cases e0
        · cases e0
      rw [← eB]
      exact IK.upd hkyT hob
    exact (i1.trans i2).trans i3
  have hIt : InvBut σ t.bv := by rw [htc]; exact Hj.inv
  obtain ⟨hIB', -⟩ := hIt.ik hnq hik
  have I3 : Inv σB := hIB'.inv fun x' hx' hc => by
    rw [hkBt] at hx'; cases hx'
    exact absurd hc (by simp [inClassR, hxT, Fl4Spec.runnable])
  -- `BlockedScActive`: an SC bound to the thread is its SC, active
  have hscA : ∀ q y1 n1, σ.kheap q = some (.schedContext y1 n1) → y1.scTcb = some t.bv →
      Fl4Spec.scActive y1 = true := by
    intro q y1 n1 hq' hyt'
    obtain ⟨xu, hku, hxu⟩ : ∃ xu : Fl4Spec.Tcb,
        σ.kheap t.bv = some (.tcb xu) ∧ xu.tcbSchedContext = some q := by
      obtain ⟨y0, hy0, ey1, -, -, -⟩ := hO.scB hq'
      obtain ⟨c, hcC, eq⟩ := J.obj.sc q y0 n1 hy0
      subst eq
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hc0 := J.c0 c hcC
      have hcS : c ∈ P1.Heap.scs H := ⟨_, (hJ.sc c y0 n1 hc0 hy0).2⟩
      obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of J.xtop.fin.1.1.1 J.blk.2.2.1 J.tcbs_eq.1.symm hcC hcS hc0 hy0
        (by rw [← ey1]; exact hyt')
      exact ⟨xu, hO.tcbF hku, hxs⟩
    rw [hk] at hku; cases hku
    have e1 : q = sc.bv := Option.some.inj (hxu.symm.trans hxsc)
    rw [e1, hky] at hq'; cases hq'
    exact hya
  have hoff : OffOK σB := fun h0 => absurd h0 (by rw [e_cons]; decide)
  have hsrtT : IpcSorted σT := KFr.isorted F2 (F1.isorted Hj.isorted fun y1 hy1 => by rw [hkM] at hy1; cases hy1)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D sB σB :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hykc, J.mcp.frame k1 hmkc, J.buf.frame kb hbkc, hRP',
      J.apart.sc_frame hks hszc, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 e_cdt e_orig e_arch hDbg, F3q.nsc (KFr.nsc F2 (F1.nsc Hj.nsc)), I3, Or.inl hact3,
      F3q.own (KFr.own F2 (F1.own Hj.own)), hoff,
      hAI3, F3q.bsa (KFr.bsa F2 (F1.bsa Hj.bsa hscA)), F3q.isorted hsrtT,
      hrun3, hblkB⟩
  have hC0 := JCs.same J hF.1 hkszc
  have hCs : JCs (L := L) (Z.mv Z.G V') sB σB := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) e_arch haoc hszc
    hF.1 hkbc hfkc hCs R (Hj.dbgK.trans (P1.Foot.dbgKeep Hj.blk (by first | exact fun _ h => h | exact Set.empty_subset _) hfoot)) e_orig
    (XTopAt.idleW_eqS J.xtop hX3 e_idle) J.zD⟩

end

end

end Fl4Proofs.P3
