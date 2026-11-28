/-
P3 (p3J gen 34): **the Reply-cap mid decode leaf proved; `midReplyFt` gone from the syscall clause**.

* **`replyXferFt_entered`**: at a `JAtZ (Z.mv G V) H Cs` state with `Entered σ` and `CKI σ`, current thread `ct`,
  reply `p ∈ Z.R`, the state `s1` after `set_thread_state ct RESTART`, `do_reply_transfer s1 ct p g` writes only
  `ProjW H Cs s1`. P3JReplyFtX's `do_reply_transfer.footNB` over P1's sets of `H` with `sE := s` (the dispatch
  state): `NoBufCap` by P3JMcFlt's `noBufCap_cki`, `BufApart` by `bufApart_blk`, every TCB's timeout-handler cap
  typed at `s` by P2's `tmoCapW_of_JAtZt`, P1's invariants at `s1` from the restarted `JAtZ` of
  `JAtZ.restartJ` (`.blk`), `TLK s s1` since the restart writes only a `KW` word (P2's `set_thread_state.kwN`);
  the `IpcWN … ∅` footprint lies in `ProjW` (`ipcWN_projW`).
* **`midDecReply_ofE`**: P3JMidReply's `midDecReply_of` with `ReplyXferFt` [J] replaced by `replyXferFt_entered`
  (the decode leaf's state is `Entered` (`BudgetAt.entered`) and `CKI` (the leaf's own premise)). Same platform facts.
* **`DispStabFootLx` [J]** {inv, midDecOther, midSpec, midRecvSw}: P3JMidReply's `DispStabFootLr` without its
  `midReplyFt` field (the other four verbatim); **`dispStabFootLk_of_Lx`**, top **`kernel_entry_runMcWKR_sysLx`**
  (globals as `_sysLr`).

Premise honesty: `DispStabFootLx` is `DispStabFootLr` minus one field, so it is implied by it. `ReplyXferFt` [J]
itself (every `JAtZ` state, no `Entered` / `CKI`) is not proved here and is no longer needed; it is not found false
(at a non-`Entered` state the restart need not keep P1's `BlkOK`, so this proof route does not reach it).

Named premise: `DispStabFootLx` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JReplyFtX
import Fl4Proofs.P3.P3JMidReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 34) **`do_reply_transfer`'s footprint after the restart, at an entered `CKI` state** (module
docstring). -/
theorem replyXferFt_entered (hA : P0.ArchTotal arI) {G : MdbGhost} {V : XVs} {Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hni : Entered σ) (hC : SInvCk.CKI σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {p : U64} (hp : p ∈ Z.R) (g : Bool) {s1 : S}
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    ipc.do_reply_transfer st arI s1 a ct p g ⦃ r => P1.WritesIn st s1 r.1 (Mc.ProjW (L := L) H Cs s1) ⦄ := by
  obtain ⟨s1', σ1, x, -, -, -, hcur, -, -, -, -, hs1', Ac', Lst', D', J1⟩ := J.restartJ hni hct
  have e : s1' = s1 := P1.ok_inj_ff (hs1'.symm.trans hs1)
  subst e
  have hctT : ct ∈ (Z.mv G V).T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hctH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct hctT
  have hpH : p ∈ P1.Heap.replies H := J.zH.2.2.1 p hp
  have hblk := J.blk
  have h0 := hblk.1.choose_spec.choose_spec
  have hf := P1.sched.set_thread_state.kwN (Kp := ∅) (Nd := False) (Sg := P1.Heap.frame H)
    (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) (Es := P1.EH H) s ct sched.TS_RESTART h0 hctH
    (Set.notMem_empty ct)
  rw [hs1', WP.spec_ok] at hf
  have hK : P1.TLK (L := L) (P1.Heap.tcbs H) s s1' :=
    P1.TLK.step h0.tcbs (P1.TLK.refl s) (P1.WritesA.w hf) fun y hy K hK h8 hh => P1.rx_notKW hblk hy hK h8 hh.1
  have hB1 := J1.blk
  refine WP.spec_mono (P1.ipc.do_reply_transfer.footNB hA (Mc.noBufCap_cki J hC) (Mc.bufApart_blk hblk)
    (fun t ht => Fl4Proofs.P2.Stall.tmoCapW_of_JAtZt J ht) s1' a ct p g (P1.BlkOK.bxi hB1) hpH hctH hK) ?_
  rintro ⟨s2, a2⟩ hW
  simp only [WP.uncurry'_pair] at hW
  exact (Fl4Proofs.P1.WritesA.w hW).mono fun b hb =>
    Mc.ipcWN_projW J1.kern.heap hB1.1.choose_spec.choose_spec.nodes hb

set_option maxHeartbeats 4000000 in
/-- (p3J gen 34) **The Reply-cap decode leaf of the mid invocation** (P3JMidReply's `midDecReply_of` with
`replyXferFt_entered`; module docstring). -/
theorem midDecReply_ofE (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hT : TimeAgree arI)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsReplyCap cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨-, p, g, rfl⟩ := hW
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  have hnib : Entered σb := BudgetAt.entered hnd hk0 (hX.entered hni) hBA
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  obtain ⟨σ1, hst⟩ := XTop.restart (L := L) (show XTop (L := L) AR s' a' σb from ⟨_, J.xtop⟩)
  have hpR : p ∈ Z.R := J.slotR hAs hc
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ (Z.mv Z.G V').T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  obtain ⟨s1, -, -, -, -, -, -, -, -, -, -, hs1, -⟩ := J.restartJ hnib hct
  have hW1 : P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s') := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  have hFt : (do
        let s1 ← sched.set_thread_state st s' ct sched.TS_RESTART
        let (s2, a1) ← ipc.do_reply_transfer st arI s1 a' ct p g
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r =>
      P1.WritesIn st s' r.2.1 (Mc.ProjW (L := L) H Cs s') ⦄ := by
    rw [hs1]; simp only [bind_ok]
    refine WP.spec_bind (replyXferFt_entered hA J hnib hCb hct hpR g hs1) ?_
    rintro ⟨s2, a2⟩ h2
    exact (WP.spec_ok _).2 (hW1.projW_trans h2)
  have hLeaf := replyLeafJSt hA hmax htu (Sched.TimeAgree.mb hT) J hnib hct hAs hc hst
    (runTmoP_recvSt _ hA hmax htu) J.stab
  have hrep := WP.spec_mono (WP.spec_and hLeaf hFt) fun r ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ =>
    (⟨h1, z, hz, h2, h3, h4⟩ : r.1 = core.result.Result.Ok () ∧ ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) σ1.curThread p.bv g σ1).1,
      RelTopM (L := L) r.2.1 z.2 ∧ (JStab (L := L) arI AR (Z.mv Z.G V') H Cs r.2.1 r.2.2 z.2 ∧
        P1.WritesIn st s' r.2.1 (Mc.ProjW (L := L) H Cs s')))
  have hq : QuietF (.Reply p g) := by simp [QuietF]
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hq hMb (fun _ _ _ h => by cases h))
    (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hq) σb _ hd.1 inv rfl)
  refine XCap.toPN arI (Or.inl ?_) (specDec_noPreK (by trivial))
  exact decode_replyDMX arI _ s' a' σb _ _ _ p g _ _ _ _ _ _ _ _ _ _ _ _ ct hct hst hrep

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

/-- (p3J gen 34) **`DispStabFootLx` [J]**: `DispStabFootLr` without `midReplyFt` (module docstring). -/
structure DispStabFootLx (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`), verbatim from `DispStabFootLr`. -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- `DispStabFootLr.midDecOther`, verbatim. -/
  midDecOther : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp) Z H Cs s a σ n c
  /-- `DispStabFootLr.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLr.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 34) **`DispStabFootLx → DispStabFootLk`** (module docstring). -/
theorem dispStabFootLk_of_Lx (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLx (L := L) arI AR MR s a σ) :
    DispStabFootLk (L := L) arI AR MR s a σ where
  inv := h.inv
  midDecReply := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    have := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midDecReply_ofE hA hnd hmax htu hT (MachPlatF.toT hM hIp) hKD hX hct
  midDecOther := h.midDecOther
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 34) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLx` only** (`hLx` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLx [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLx : DispStabFootLx (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLk hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLk_of_Lx hA hnd hM hIp hKD hT hmax htu hLx)

end

end Fl4Proofs.P3.Mc
