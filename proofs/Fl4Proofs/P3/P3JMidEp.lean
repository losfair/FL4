/-
P3 (p3J gen 35): **the mid decode leaf of the Endpoint cap proved**; `midDecRest` reduced to the remaining caps.

The mid class invokes the looked-up cap with `blocking = is_call = false`, `can_donate = true`: on an Endpoint cap
(with the send right) FL4 restarts the caller and runs `send_ipc s1 … false false b g gr true ct p`.

* `JAtZ.restartFactsSt`: XTopJointTcbInstall's `JAtZ.restartJ` with the facts `sendLeafJ2` derives at the restarted
  state (the caller `Restart`, current, `Entered`, in no ready queue; `JAtZ` at the same `Z`).
* `JAtZ.curScNZ`: under `CurInv`, the current thread's SC word is not `0` (XTopJointRecvMid's `curScAc` and
  `JAtZ.c0`): P2's `send_ipc.footN` side condition for a donating send.
* **`midDecEp_of`**: `MidDecStW (KW ∧ IsEpCap)` from `SInvX σ` and `ct ≠ idle` at the entry (platform facts [P]
  `hA`, `hnd`, `hMT`, `hKD`, as gen 34's `midDecEasy_of`). Send right off: `InvalidCapability` on both sides
  (IpcSendTop's `decode_endpointDMX`). Send right on: the stable send P3JSendSt's `sendAfterRestartSt` (the
  dispatch state's `cnf` / `ctnq` by XTopJointKEntry27S's `sinvB_disp` and `SInvX.ctQ`, as P3JRecvCls), its
  footprint P3JSendFt's `sendIpcProjW` at the restarted state with `sE :=` the dispatch state (`noBufCap_cki`,
  `bufApart_blk`, `TLK` of the restart as gen 34), the restart's footprint `stsProjW`, `MR` by `XCapP.mrT` (an
  Endpoint cap is `QuietF`), never preempted (`specDec_noPreK`).
* `midDecRest_of_ep`: gen 34's `midDecRest` predicate from `midDecEp_of` and the rest (`¬ IsEpCap` added).
* **`DispStabFootLn` [J]** {inv, midDecRest, midSpec, midRecvSw}: P3JMidNtfn's `DispStabFootLe` with `midDecRest`
  restricted to `¬ IsEpCap`; **`dispStabFootLe_of_Ln`**, top **`kernel_entry_runMcWKR_sysLn`** (globals as
  `_sysLe`).

Premise honesty: `DispStabFootLn.midDecRest` is `DispStabFootLe.midDecRest` at a smaller cap predicate
(`MidDecStW` is antitone in it), the other fields verbatim, so `DispStabFootLn` is implied by `DispStabFootLe`.

Named premise: `DispStabFootLn` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JSendSt
import Fl4Proofs.P3.P3JSendFt
import Fl4Proofs.P3.P3JMidNtfn
import Fl4Proofs.P3.XTopJointRecvMid
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 35) The Endpoint caps. -/
def IsEpCap : capability.Cap → Prop
  | .Endpoint .. => True
  | _ => False

theorem isEp_cases {cp : capability.Cap} (h : IsEpCap cp) : ∃ p b sd rv g gr, cp = .Endpoint p b sd rv g gr := by
  cases cp <;> simp_all [IsEpCap]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The restart's facts for a send** (module docstring). -/
theorem JAtZ.restartFactsSt {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hnq : ∀ d q, σ.curThread ∉ σ.readyQueues d q) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∃ (s1 : S) (σ1 : Fl4Spec.State Unit) (x : Fl4Spec.Tcb), Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 ∧ ct ∈ Z.T ∧ σ.curThread = ct.bv ∧
      σ1.kheap ct.bv = some (.tcb { x with tcbState := .restart }) ∧ σ1.curThread = ct.bv ∧ Entered σ1 ∧
      (∀ d q, σ1.curThread ∉ σ1.readyQueues d q) ∧
      ∃ (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64), JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 s1 ar σ1 := by
  obtain ⟨-, xr0, hkr, hrun0⟩ := J.curRunnable hni hct
  obtain ⟨s1, σ1', x, -, hst1, hkx, hcur, eσ1, -, hidl, hcur1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hrun : Fl4Spec.runnable x.tcbState = true := by rw [hkx] at hkr; cases hkr; exact hrun0
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hcq, -⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hcq.cur] at h; exact h
  have hctT : ct ∈ Z.T := hct' ▸ hcq.curT
  set xr : Fl4Spec.Tcb := { x with tcbState := .restart }
  have hkt1 : σ1'.kheap ct.bv = some (.tcb xr) := by
    rw [eσ1, (stsAct_fields _ _).1]; simp [Notif.updK]
  have hc1 : σ1'.curThread = ct.bv := hcur1.trans hcur
  have hsch : Fl4Spec.schedulable ct.bv σ = true := by
    have h := ct_schedulable (J.curInv (by rw [hni.2]; simp)) J.act J.inv (hcur ▸ hkx) hrun
    rw [hcur] at h; exact h
  have hsch1 : Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb xr)) = true := by
    rw [schedulable_updK_tcb (y := xr) (y' := x) (by rw [hrun]; rfl) rfl]
    exact (schedulable_heap (σ := σ) (σ' := Notif.updK σ ct.bv (.tcb x))
      (by simp only [Notif.updK_kheap]; exact Function.update_eq_self_iff.2 hkx.symm) rfl ct.bv).trans hsch
  have hres1 : σ1'.schedulerAction = .resumeCurThread := by
    rw [eσ1]; unfold Notif.stsAct
    rw [if_neg (fun h => by simp [hsch1] at h)]
    exact hni.2
  have hti1 : σ1'.curThread ≠ σ1'.idleThread := by rw [hcur1, hidl]; exact hni.1
  have hrq1 : σ1'.readyQueues = σ.readyQueues := by
    rw [eσ1]; unfold Notif.stsAct; split <;> rfl
  have hnq1 : ∀ d q, σ1'.curThread ∉ σ1'.readyQueues d q := by
    rw [hrq1, hcur1]; exact hnq
  exact ⟨s1, σ1', x, hst1, hs1, hctT, hcur, hkt1, hc1, ⟨hti1, hres1⟩, hnq1, Ac1, Lst1, D1, J1⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The current thread's SC word is not `0`** under `CurInv` (module docstring). -/
theorem JAtZ.curScNZ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) : L.mem s (P1.scA (L.curW s)) ≠ 0#u64 := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -⟩ := CurInv.facts hS J.inv hC
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  rw [(J.curScAc hC hni).1, ecsc]
  exact J.c0 _ hscC

variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The mid decode leaf of the Endpoint cap** (module docstring). -/
theorem midDecEp_of (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsEpCap cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨p, b, sd, rv, g, gr, rfl⟩ := isEp_cases hW.2
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  have hnib : Entered σb := BudgetAt.entered hnd hk0 (hX.entered hni) hBA
  obtain ⟨-, ek, ect, -, -, eq⟩ := BudgetAt.shape27 hnd hk0 hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  obtain ⟨-, hcnf⟩ := SInvAll.sinvB_disp (x' := Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
    hX.sb hni hk0 rfl rfl ek' ect
  have hq : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect, eq]; exact hX.ctQ
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  have hqF : QuietF (.Endpoint p b sd rv g gr) := by simp [QuietF]
  obtain ⟨s1, σ1, x, hst1, hs1, hctT, hcur, hk1, hc1, hen1, hnq1, Ac1, Lst1, D1, J1⟩ := J.restartFactsSt hnib hq hct
  have hW1 : P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s') := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  have hblk := J.blk
  have h0 := hblk.1.choose_spec.choose_spec
  have hf := P1.sched.set_thread_state.kwN (Kp := ∅) (Nd := False) (Sg := P1.Heap.frame H)
    (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) (Es := P1.EH H) s' ct sched.TS_RESTART h0 (J.zH.1 ct hctT)
    (Set.notMem_empty ct)
  rw [hs1, WP.spec_ok] at hf
  have hK : P1.TLK (L := L) (P1.Heap.tcbs H) s' s1 :=
    P1.TLK.step h0.tcbs (P1.TLK.refl s') (P1.WritesA.w hf) fun y hy K hK h8 hh =>
      P1.rx_notKW hblk hy hK h8 hh.1
  have hsend : (do
      let s1 ← sched.set_thread_state st s' ct sched.TS_RESTART
      let (s2, a1) ← endpoint.send_ipc st arI s1 a' false false b g gr true ct p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
        ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) false false b.bv g gr true σ1.curThread p.bv σ1).1,
          RelTopM (L := L) r.2.1 z.2 ∧ (JStab (L := L) arI AR (Z.mv Z.G V') H Cs r.2.1 r.2.2 z.2 ∧
            P1.WritesIn st s' r.2.1 (Mc.ProjW (L := L) H Cs s')) ⦄ := by
    have hpE : p ∈ (Z.mv Z.G V').E := J.slotE hAs hc
    have hHe : H p = some .ep := J.zH.2.1 p hpE
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := J1.blk
    have hcb1 := J1.canBlockCur hctT hc1 hk1 rfl hen1 hnq1
    have hcw : L.curW s1 = ct := by
      have h := cur_thread_eq (L := L) s1
      exact P1.eq_of_bv ((J1.curEq h).1.symm.trans hc1)
    have hdon : true = true → L.mem s1 (P1.scA ct) ≠ 0#u64 := fun _ => by
      rw [← hcw]; exact J1.curScNZ (J1.curInv (by rw [hen1.2]; simp)) hen1.1
    have hFt := Mc.sendIpcProjW hA J.kern.heap (Mc.noBufCap_cki J hCb) (Mc.bufApart_blk hblk) s1 a' false false b g gr
      true ct p Q1 R1 q1 hB1 hX1 hS1 hSg1 hcb1 hdon hHe hK.bufK
    rw [hs1]; simp only [bind_ok]
    refine WP.spec_bind (WP.spec_and (sendAfterRestartSt hA J hnib hq hcnf hct hAs hc hst1 hs1 false false g gr true)
      hFt) ?_
    rintro ⟨s2, a2⟩ ⟨⟨z, hz, G2, V2, Ac2, Lst2, D2, J2⟩, hW2⟩
    exact (WP.spec_ok _).2 ⟨rfl, z, hz, J2.xtop.relTop, ⟨G2, V2, Ac2, Lst2, D2, J2⟩, hW1.projW_trans hW2⟩
  refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hqF hMb (fun _ _ _ h => by cases h))
    (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hqF) σb _ hd.1 inv rfl)
  refine XCap.toPN arI (Or.inl ?_) (specDec_noPreK (by trivial))
  exact decode_endpointDMX arI _ s' a' σb _ _ _ p b sd rv g gr _ _ _ _ _ _ _ _ _ _ _ _ ct hct hX0 hst1
    fun _ => hsend

/-- (p3J gen 35) **gen 34's `midDecRest` from the Endpoint leaf and the remaining caps** (module docstring). -/
theorem midDecRest_of_ep (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStW (L := L) arI AR MR
      (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp) Z H Cs s a σ n c) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp)
      Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hE : IsEpCap cp
  · exact midDecEp_of hA hnd hMT hKD hX hni σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn
      info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, hE⟩
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, hW.2.1, hW.2.2, hE⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 35) **`DispStabFootLn` [J]**: `DispStabFootLe` with `midDecRest` restricted to the caps other than
Endpoint (module docstring). -/
structure DispStabFootLn (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`), verbatim from `DispStabFootLe`. -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- `DispStabFootLe.midDecRest` for the caps that are not `IsEpCap`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR
          (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp) Z H Cs s a σ n c
  /-- `DispStabFootLe.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLe.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 35) **`DispStabFootLn → DispStabFootLe`** (module docstring). -/
theorem dispStabFootLe_of_Ln (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLn (L := L) arI AR MR s a σ) :
    DispStabFootLe (L := L) arI AR MR s a σ where
  inv := h.inv
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    have := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midDecRest_of_ep hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLn` only** (`hLn` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLn [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLn : DispStabFootLn (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLe hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLe_of_Ln hA hnd hM hIp hKD hLn)

end

end Fl4Proofs.P3.Mc
