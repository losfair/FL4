/-
P3 (DESIGN.md §9), scheduling contexts: **`handle_timeout` of the current
thread at the state inside `charge_budget` (a `JTH` state) with receivers
waiting on its timeout handler's endpoint** (KENTRY-PLAN kp17 (1)): ScChargeTA's
`JTH.tmoBlockJA` up to `set_fault` (the handler cap at the hole and the
base), then the virtual base (ScTmoCtBase `JTH.tmoBaseCtJ`) and the send
to the queue head: `JAtZ.sendTmoRecvCtIJ` (the sender left `Inactive`) or
`JAtZ.sendTmoRecvCtPJ` (the reply pushed), as XTopJointFaultTmo's
`JAtZ.runTmoRecvJ`. Platform facts `hmax`/`htu` [P] as there.
-/
import Fl4Proofs.P3.ScTmoCtRecvP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec
variable {σ : State Unit} {t sc : U64} {x : Tcb} {y : SchedContext} {n : Nat} {b : U64}

theorem tmoCtSt_kh {q : ObjRef} (h1 : q ≠ t.bv) (h2 : q ≠ sc.bv) : (tmoCtSt σ t sc x y n b).kheap q = σ.kheap q := by
  simp [tmoCtSt, Ipc.tmoSt, updSc, updK, stsAct_kheap, h1, h2]

theorem tmoCtSt_kt (hst : sc.bv ≠ t.bv) : (tmoCtSt σ t sc x y n b).kheap t.bv =
    some (.tcb { x with tcbState := .inactive, tcbFault := some (.timeout b.bv) }) := by
  simp [tmoCtSt, Ipc.tmoSt, updSc, updK, stsAct_kheap, Ne.symm hst]

theorem tmoCtSt_ksc : (tmoCtSt σ t sc x y n b).kheap sc.bv =
    some (.schedContext { y with scConsumed := (0#u64 : U64).bv } n) := by
  simp [tmoCtSt, Ipc.tmoSt, updSc, updK]

theorem tmoCtSt_sk : Sk σ (tmoCtSt σ t sc x y n b) := by
  unfold tmoCtSt Notif.stsAct
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tmoCtSt_rq : (tmoCtSt σ t sc x y n b).readyQueues = σ.readyQueues := by
  unfold tmoCtSt Notif.stsAct
  split_ifs <;> rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 64000000 in
/-- **`handle_timeout` of the current thread at a `JTH` state, receivers
waiting on the handler's endpoint** (module docstring). -/
theorem JTH.tmoRecvJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hj : JTH (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {t : U64} (ht : t ∈ Z.T)
    (htc : t.bv = σ.curThread) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrr : x.tcbState = .running ∨ x.tcbState = .restart)
    {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv) (hscc : sc.bv = σ.curSc)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : x.tcbTimeoutHandler = .endpointCap p bd r)
    (hkl : ∃ l, σ.kheap p = some (.endpoint (.recvEP l)))
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread) (hnq : NotQueued σ t.bv) (hidt : σ.idleThread ≠ t.bv)
    (b : U64) :
    faults.handle_timeout st arI s a t (error.Fault.Timeout b) ⦃ res => ∃ z ∈
      (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv) σ).1,
      ∃ (V : XVs) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D' res.1 res.2 z.2 ⦄ := by
  have J := Hj.j0
  have hO := Hj.ksc
  have hP0 := J.ip
  have hks0 : L.ksb s = L.ksb s0 := Hj.ws.1
  have hI0 := J.xtop.irelK J.ks J.buf
  have hI' := Hj.xtop.irelK (by rw [hks0]; exact J.ks) Hj.buf
  have hI : IRel st Z.th σ0.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := by
    rw [← Hj.arch]; exact hI'
  have hS := Hj.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hta := hP0.e.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  have hk0 : σ0.kheap t.bv = some (.tcb x) := hO.tcbB hk
  have hD : t ∉ D := fun h => by
    have hd := J.jcov.dead t h
    have h1 := (hd.1 htH).1
    obtain ⟨x1, hk1, hTR⟩ := hI0.1.tcb t ht
    rw [hk0] at hk1; cases hk1
    have hst := hTR.st
    rw [← stA_tStA, h1] at hst
    unfold sched.TS_INACTIVE at hst
    rcases hrr with e | e <;> rw [e] at hst <;> simp [tsCode] at hst
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ0.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  -- the handler cap at the base, its endpoint, the cover
  obtain ⟨⟨G0, hB0⟩, -⟩ := hI0.2.1
  have hth0 : Z.th t = some .tcb := hB0.tcbT hk0
  obtain ⟨xh, cv, hkh, hcv, hca⟩ := hB0.2.1.1.timeoutCap hth0
  rw [hk0] at hkh; cases hkh
  have habs := hca.2
  rw [hth] at habs
  obtain ⟨ptr, bdg, sd, rv, g, gr, rfl⟩ : ∃ ptr bdg sd rv g gr, cv = .Endpoint ptr bdg sd rv g gr := by
    cases cv <;> simp [absCap] at habs; exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs
  obtain ⟨hp, hbd, hr⟩ := habs
  subst hp hbd hr
  have hAS : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 4) := ⟨t, rfl, Or.inr ⟨hth0, 4, by decide, rfl⟩⟩
  have hcv' : capAt (L.mem s0) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 4)) = ok (.Endpoint ptr bdg sd rv g gr) := by
    rw [tcbSlot4_eq]; exact hcv
  have hpE : ptr ∈ Z.E := J.slotE hAS hcv'
  obtain ⟨xe, hke0, -⟩ := hI0.1.ep ptr hpE
  have hke : σ.kheap ptr.bv = some (.endpoint xe) := hO.othF hke0 (fun _ _ e => by cases e)
  obtain ⟨l, hkl'⟩ := hkl
  rw [hke] at hkl'
  cases hkl'
  have hpt : ptr.bv ≠ t.bv := fun e => by rw [e, hk] at hke; cases hke
  have hHe : H ptr = some .ep := J.zH.2.1 ptr hpE
  have hfit := J.kern.heap.fits ptr _ hHe
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap (P1.WritesIn.refl s0 _) hAS.isSlot hcv' (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_ep ptr bdg sd rv g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  -- the FL4 step from the base to the hole (`CnStep`)
  have hC1 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0 s σ :=
    ⟨Hj.ws.mono fun b hb => Or.inl (Or.inl hb), SzKeepC.of hO.szKeep⟩
  -- `handle_timeout`: the handler cap at the hole
  obtain ⟨⟨G6, hB6⟩, -⟩ := hI.2.1
  obtain ⟨xh6, cv6, hkh6, hcv6, hca6⟩ := hB6.2.1.1.timeoutCap (hB6.tcbT hk)
  rw [hk] at hkh6; cases hkh6
  have habs6 := hca6.2
  rw [hth] at habs6
  unfold faults.handle_timeout
  rw [tcb_slot_timeout]
  apply ok_bind_spec
  rw [slot_cap_eq, hcv6]
  apply ok_bind_spec
  cases cv6
  case Endpoint ptr' bdg' sd' rv' g' gr' =>
    simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs6
    obtain ⟨hp', hbd', hr'⟩ := habs6
    obtain rfl : ptr = ptr' := (P1.eq_of_bv hp').symm
    obtain rfl : bdg = bdg' := (P1.eq_of_bv hbd').symm
    have hg : g' = g := by have := congrArg (fun R => decide (Fl4Spec.Rights.allowGrant ∈ R)) hr'; simpa [rights_grant] using this
    have hgr : gr' = gr := by
      have := congrArg (fun R => decide (Fl4Spec.Rights.allowGrantReply ∈ R)) hr'; simpa [rights_grantReply] using this
    obtain rfl : g = g' := hg.symm
    obtain rfl : gr = gr' := hgr.symm
    refine WP.spec_bind (Pₘ := fun r : Bool × S × A => ∃ z ∈ (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv) σ).1,
      ∃ (V : XVs) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D' r.2.1 r.2.2 z.2) ?_ ?_
    swap
    · rintro ⟨b0, s2, a2⟩ hr0
      exact (WP.spec_ok _).2 hr0
    unfold faults.send_fault_ipc
    dsimp only
    -- `set_fault`
    set x2 : Fl4Spec.Tcb := { x with tcbFault := some (.timeout b.bv) } with hx2
    set σf := updK σ t.bv (.tcb x2) with hσf
    refine WP.spec_bind (WP.spec_and (WP.spec_and (set_fault_timeout_top hP0 hI ht hk b)
      (set_fault_timeout_eq s t b)) (WP.spec_and (P1.faults.set_fault.blk (U := ∅) s t (error.Fault.Timeout b)
        (t0 := t) Hj.blk htH (fun _ h => by simp at h) ?hcb6)
        (P1.faults.set_fault.kw (Cs := Cs) (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
          (Es := P1.EH H) s t (error.Fault.Timeout b) hTH htH))) ?_
    case hcb6 =>
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
        exact (hSc.act _ hiS).2 (fun e => hmx (by rw [e]; rfl))
    rintro s7 ⟨⟨⟨hsp7, hI7⟩, hs7⟩, ⟨hblk7, -, hcb7⟩, hfoot7⟩
    have hkf : σf.kheap t.bv = some (.tcb x2) := by simp [hσf, updK]
    have hkfp : ∀ q, q ≠ t.bv → σf.kheap q = σ.kheap q := by
      intro q hq'; rw [hσf]; simp only [updK, Function.update_of_ne hq']
    -- the FL4 step of `set_fault`
    have hC2 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ s7 σf := by
      refine ⟨?_, SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := x2) (fun q hq' => by simp [hσf, updK, hq']) hkf)⟩
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
    have hW7 : P1.WritesIn st s s7 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hC2.1
    have hst : sc.bv ≠ t.bv := fun e => by rw [e, hk] at hky; cases hky
    obtain ⟨sB, hwB, hfB, V0, J0⟩ := Hj.tmoBaseCtJ hAT hmax htu ht htc hk hrr hsc hxsc hscc hky hya hres hnq hidt b
    have hrun : Fl4Spec.runnable x.tcbState = true := by rcases hrr with e | e <;> rw [e] <;> rfl
    have hI7' : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s7
        (updK σ t.bv (.tcb { x with tcbState := x.tcbState, tcbFault := some (.timeout b.bv) })) := by
      rw [Hj.arch]; exact hI7
    -- the receivers waiting on the endpoint
    obtain ⟨-, xs, hxs0, hq, hQ, -⟩ := hI.1.toE.at_ep hpE hke
    obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons] at hq
    subst hq
    have fin : ∀ z : Unit × Fl4Spec.State Unit, z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr false t.bv ptr.bv
        (updK σ t.bv (.tcb { x with tcbState := x.tcbState, tcbFault := some (.timeout b.bv) }))).1 →
        z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv
          (decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr))
          (decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr)) false t.bv ptr.bv
          (updK σ t.bv (.tcb { x with tcbFault := some (.timeout b.bv) }))).1 := by
      intro z hz
      rw [rights_grant, rights_grantReply]
      exact hz
    by_cases hpush : (g = true ∨ gr = true) ∧ ∀ xd, σ.kheap d'.bv = some (.tcb xd) →
        ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
    · refine WP.spec_bind (J0.sendTmoRecvCtPJ hAT hmax htu ht hk htc hres hnq hidt hsc hxsc hky b
        (fun q h1 h2 => tmoCtSt_kh h1 h2) (tmoCtSt_kt hst) tmoCtSt_ksc tmoCtSt_sk tmoCtSt_rq hwB hfB
        (ts := x.tcbState) hrun hI7' hblk7 hW7 hfoot7 hcb7 hpE hke bdg g gr hpush.1 hD hya hpush.2) ?_
      rintro ⟨s', a'⟩ ⟨z, hz, V, Lst', hJ⟩
      exact (WP.spec_ok _).2 ⟨((), z.2), handleTimeout_mem hk hth _ (fin z hz), V, Lst', D, hJ⟩
    · have hno : (g = false ∧ gr = false) ∨ ∀ xd, σ.kheap d'.bv = some (.tcb xd) →
          ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none := by
        by_cases hgg : g = true ∨ gr = true
        · right
          intro xd hkd e' rep dd hst'
          by_contra hr
          apply hpush
          refine ⟨hgg, fun xd' hkd' e'' rep' dd' hst'' => ?_⟩
          rw [hkd] at hkd'; cases hkd'
          rw [hst'] at hst''; cases hst''; exact hr
        · left
          have h1 : g ≠ true := fun h => hgg (Or.inl h)
          have h2 : gr ≠ true := fun h => hgg (Or.inr h)
          exact ⟨by simpa using h1, by simpa using h2⟩
      refine WP.spec_bind (J0.sendTmoRecvCtIJ hmax htu ht hk htc hres hsc hxsc hky b
        (fun q h1 h2 => tmoCtSt_kh h1 h2) (tmoCtSt_kt hst) tmoCtSt_ksc tmoCtSt_sk tmoCtSt_rq hwB hfB
        (ts := x.tcbState) hrun hI7' hblk7 hW7 hfoot7 hcb7 hpE hke bdg g gr hno) ?_
      rintro ⟨s', a'⟩ ⟨z, hz, V, Lst', hJ⟩
      exact (WP.spec_ok _).2 ⟨((), z.2), handleTimeout_mem hk hth _ (fin z hz), V, Lst', D, hJ⟩
  all_goals simp [absCap] at habs6

end

end

end Fl4Proofs.P3
