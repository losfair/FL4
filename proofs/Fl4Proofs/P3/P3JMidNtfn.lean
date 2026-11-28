/-
P3 (p3J gen 34): **the mid decode leaves of the Null, Zombie and Notification caps proved**; `midDecOther`
reduced to the remaining `KW` caps.

* **`Mc.sendSignalProjW`**: from P1's `BlkOK` over `H`'s sets and `NoBufCap` (every IPC-buffer lookup `0`, so P1's
  `BufAt` at `U = ∅`: `bufAt_noBuf`), FL4's `send_signal` writes only `ProjW H Cs s`: P1's `send_signal.tinvF`
  (`FootDU … ∅`) and P3JFinW's `send_signal.idlF` (every core's node words 8 / 32 kept), joined by P3JMcFin's
  `projW_of_footDU_idl`.
* `BudgetAt.nativeScopeM`: `NativeScope` at the dispatch state (spec `ns_fl4SyscallFaultIP`, `ns_updateTimeStamp`,
  `ns_checkBudgetRestart`).
* `IsEasyCap` (Null, Zombie, Notification), `isEasy_cases`.
* **`midDecEasy_of`**: `MidDecStW (KW ∧ IsEasyCap)` from `SInvX σ` and `ct ≠ idle` at the entry (platform facts [P]
  `hA`, `hnd`, `hT` (`min_budget`), `hMT`, `hKD`). Null / Zombie: FL4 and the spec both answer
  `InvalidCapability` at once (XTopJointKEntry23P's text); the post holds at the dispatch state itself. Notification:
  IpcSendTop's `decode_notificationDMX` with the restart (`JAtZ.restartJ`, footprint `stsProjW`) and ScSignalJN's
  `JAtZ.signal_atN` at the restarted `JAtZ` (it already ends at the entry's `H`, `Cs`: a `JStab` post), the
  signal's footprint by `sendSignalProjW` (`NoBufCap` at the restarted state from `noBufCap_cki` at the dispatch
  state and P3JReplyFtX's `TLK`), `MR` by `XCapP.mrT` (the three caps are `QuietF`).
* `midDecOther_of_rest`: `midDecOther` from `midDecEasy_of` and the rest (`KW ∧ ¬ IsReplyCap ∧ ¬ IsEasyCap`).
* **`DispStabFootLe` [J]** {inv, midDecRest, midSpec, midRecvSw}: P3JReplyFtTop's `DispStabFootLx` with
  `midDecOther` restricted to `¬ IsEasyCap`; **`dispStabFootLx_of_Le`**, top **`kernel_entry_runMcWKR_sysLe`**
  (globals as `_sysLx`).

Premise honesty: `midDecRest` is `midDecOther` restricted to fewer caps (`MidDecStW` is antitone in its cap
predicate), so `DispStabFootLe` is implied by `DispStabFootLx`.

Named premise: `DispStabFootLe` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JReplyFtTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {H : P1.Heap} {Cs Ac : Set U64}

/-- P1's `BufAt` at `U = ∅` from `NoBufCap`. -/
theorem bufAt_noBuf {T Sg Scs : Set U64} {Z : U64 → Nat} {s : S} (hN : P1.NoBufCap (L := L) T s) :
    P1.BufAt st T Cs H Sg Scs Z ∅ s :=
  ⟨fun b hb => absurd hb (Set.notMem_empty b), fun y hy => by
    rw [P1.lookup_ipc_buffer_noBuf hN hy true, WP.spec_ok]; exact fun h => (h rfl).elim⟩

/-- (p3J gen 34) **`send_signal` writes only `ProjW`** (module docstring). -/
theorem sendSignalProjW (hA : P0.ArchTotal ar) (hH : P1.HeapOK H) {s : S} {a : A}
    (h : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s)
    (hNB : P1.NoBufCap (L := L) (P1.Heap.tcbs H) s) {n : U64} (hn : H n = some .ntfn) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hBA : P1.BufAt st (P1.Heap.tcbs H) Cs H (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s :=
    bufAt_noBuf hNB
  refine WP.spec_mono (WP.spec_and (P1.notification.send_signal.tinvF hA s a n badge h hn hn hBA.1 hBA.2)
    (Fl4Proofs.P2.Stall.notification.send_signal.idlF hA s a n badge h hn hn hBA.1 hBA.2)) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh
  obtain ⟨⟨-, Fd, -, -⟩, K⟩ := hh
  exact projW_of_footDU_idl hH h.1.choose_spec.choose_spec.nodes Fd K

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 34) `NativeScope` at the dispatch state of the entry. -/
theorem BudgetAt.nativeScopeM {σ σb : Fl4Spec.State Unit} (hN : NativeScope σ) (h : BudgetAt σ σb true) :
    NativeScope σb := by
  obtain ⟨σ0, h0, hb⟩ := h
  have hN0 : NativeScope σ0 := SInv.ns_fl4SyscallFaultIP σ.curThread σ hN _ h0
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hb
  exact SInv.ns_checkBudgetRestart σu (SInv.ns_updateTimeStamp σ0 hN0 _ hu) _ h2

/-- (p3J gen 34) The caps whose mid decode leaf is proved here. -/
def IsEasyCap : capability.Cap → Prop
  | .Null => True
  | .Zombie .. => True
  | .Notification .. => True
  | _ => False

theorem isEasy_cases {cp : capability.Cap} (h : IsEasyCap cp) :
    cp = .Null ∨ (∃ p zt n, cp = .Zombie p zt n) ∨ ∃ p b w r, cp = .Notification p b w r := by
  cases cp <;> simp_all [IsEasyCap]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 34) **The mid decode leaves of the Null, Zombie and Notification caps** (module docstring). -/
theorem midDecEasy_of (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hT : TimeAgree arI)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsEasyCap cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  have hnib : Entered σb := BudgetAt.entered hnd hk0 (hX.entered hni) hBA
  have hNb : NativeScope σb := BudgetAt.nativeScopeM hX.nativeScope hBA
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  rcases isEasy_cases hW.2 with rfl | ⟨p, zt, nn, rfl⟩ | ⟨p, b, w, r, rfl⟩
  · have hq : QuietF .Null := by simp [QuietF]
    refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hq hMb (fun _ _ _ h => by cases h))
      (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hq) σb _ hd.1 inv rfl)
    refine XCap.toPN arI (Or.inl ?_) (specDec_noPreK (by trivial))
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  · have hq : QuietF (.Zombie p zt nn) := by simp [QuietF]
    refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hq hMb (fun _ _ _ h => by cases h))
      (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hq) σb _ hd.1 inv rfl)
    refine XCap.toPN arI (Or.inl ?_) (specDec_noPreK (by trivial))
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  · have hq : QuietF (.Notification p b w r) := by simp [QuietF]
    obtain ⟨hcur, -⟩ := J.curEq hct
    have hctT : ct ∈ (Z.mv Z.G V').T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
    obtain ⟨s1, σ1, x, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hnib hct
    have hN1 : NativeScope σ1 := (SInv.nativeScopeS_iff σ1).1 (SInv.ns_setThreadState σb.curThread .restart
      (by intro e; cases e) σb ((SInv.nativeScopeS_iff σb).2 hNb) ((), σ1) (by rw [hst1]; exact Set.mem_singleton _))
    have hW1 : P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s') := by
      have h := stsProjW J hctT sched.TS_RESTART
      rw [hs1, WP.spec_ok] at h; exact h
    have hpN : p ∈ Z.N := (J.slotN hAs hc).1
    have hpH : H p = some .ntfn := J.zH.2.2.2 p hpN
    have hblk := J.blk
    have h0 := hblk.1.choose_spec.choose_spec
    have hf := P1.sched.set_thread_state.kwN (Kp := ∅) (Nd := False) (Sg := P1.Heap.frame H)
      (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) (Es := P1.EH H) s' ct sched.TS_RESTART h0 (J.zH.1 ct hctT)
      (Set.notMem_empty ct)
    rw [hs1, WP.spec_ok] at hf
    have hK : P1.TLK (L := L) (P1.Heap.tcbs H) s' s1 :=
      P1.TLK.step h0.tcbs (P1.TLK.refl s') (P1.WritesA.w hf) fun y hy K hK h8 hh =>
        P1.rx_notKW hblk hy hK h8 hh.1
    have hNB1 : P1.NoBufCap (L := L) (P1.Heap.tcbs H) s1 := (Mc.noBufCap_cki J hCb).of_bufK hK.bufK
    have hsend : (do
        let s1 ← sched.set_thread_state st s' ct sched.TS_RESTART
        let (s2, a1) ← notification.send_signal st arI s1 a' p b
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
          ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1).1,
            RelTopM (L := L) r.2.1 z.2 ∧ (JStab (L := L) arI AR (Z.mv Z.G V') H Cs r.2.1 r.2.2 z.2 ∧
              P1.WritesIn st s' r.2.1 (Mc.ProjW (L := L) H Cs s')) ⦄ := by
      rw [hs1]; simp only [bind_ok]
      refine WP.spec_bind (WP.spec_and (J1.signal_atN hA (Sched.TimeAgree.mb hT) hN1 p b hpN)
        (Mc.sendSignalProjW hA J.kern.heap J1.blk hNB1 hpH b)) ?_
      rintro ⟨s2, a2⟩ ⟨⟨σ', V'', Ac'', Lst'', D'', hsp, -, J'⟩, hW2⟩
      exact (WP.spec_ok _).2 ⟨rfl, ((), σ'), by rw [hsp]; exact Set.mem_singleton _, J'.xtop.relTop,
        ⟨_, _, _, _, _, J'⟩, hW1.projW_trans hW2⟩
    refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hq hMb (fun _ _ _ h => by cases h))
      (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hq) σb _ hd.1 inv rfl)
    refine XCap.toPN arI (Or.inl ?_) (specDec_noPreK (by trivial))
    exact decode_notificationDMX arI _ s' a' σb _ _ _ p b w r _ _ _ _ _ _ _ _ _ _ _ _ ct hct hX0 hst1
      fun _ => hsend

/-- (p3J gen 34) **`midDecOther` from the leaves of the remaining caps** (module docstring). -/
theorem midDecOther_of_rest (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hT : TimeAgree arI)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp)
      Z H Cs s a σ n c) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hE : IsEasyCap cp
  · exact midDecEasy_of hA hnd hT hMT hKD hX hni σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn
      info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, hE⟩
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, hW.2, hE⟩

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

/-- (p3J gen 34) **`DispStabFootLe` [J]**: `DispStabFootLx` with `midDecOther` restricted to the caps other than
Null, Zombie and Notification (module docstring). -/
structure DispStabFootLe (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`), verbatim from `DispStabFootLx`. -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- `DispStabFootLx.midDecOther` for the caps that are not `IsEasyCap`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp)
          Z H Cs s a σ n c
  /-- `DispStabFootLx.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLx.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 34) **`DispStabFootLe → DispStabFootLx`** (module docstring). -/
theorem dispStabFootLx_of_Le (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLe (L := L) arI AR MR s a σ) :
    DispStabFootLx (L := L) arI AR MR s a σ where
  inv := h.inv
  midDecOther := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    have := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midDecOther_of_rest hA hnd hT (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 34) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLe` only** (`hLe` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLe [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLe : DispStabFootLe (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLx hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLx_of_Le hA hnd hM hIp hKD hT hLe)

end

end Fl4Proofs.P3.Mc
