/-
P3 (p3J gen 33): **the mid invocation's Reply-cap decode leaf reduced to `do_reply_transfer`'s footprint**.

P3JMidDecK's `DispStabFootLk` asks, for a Reply cap `Reply p g` in the looked-up slot (`midDecReply`), the decode
leaf `XCapP (MidX …) (MidXP …)`: the stable post (`JStab Z H Cs`), `MR`, and the footprint `ProjW H Cs s'`. The
first two are StPostReply's `replyLeafJSt` (with `runTmoP_recvSt`) through IpcSendTop's `decode_replyDMX`, the
preempted outcome excluded by `specDec_noPreK`; `MR` as StPostInv's `handle_invocation_replyJSt` but from
`MachPlatT` (the tops' `MachPlatF` + `IpiF`, not `MachPlat`): **`TopPostDMXP.mrT`**, **`TopPostRMX.mrT`**,
**`XCapP.mrT`** (KEntry38's `….mr` with `msF_mrT`). The `set_thread_state … RESTART` before the transfer is in
`ProjW` (P3JMidInv's `stsProjW`). Left: the transfer's own footprint.

* **`ReplyXferFt Z H Cs` [J]** (FL4 only): at every state `JAtZ (Z.mv G V) H Cs` with current thread `ct`, every
  reply object `p ∈ Z.R`, the state `s1` after `set_thread_state ct RESTART`, `do_reply_transfer s1 ct p g` writes
  only `ProjW H Cs s1`.
* **`midDecReply_of`**: `SInvX σ`, `ct ≠ idle` at the entry and `ReplyXferFt` give `midDecReply`'s
  `MidDecStW (KW ∧ IsReplyCap)` (platform facts [P] `hA`, `hnd`, `hmax`, `htu`, `hT` (`TimeAgree.mb` for
  `min_budget`), `hMT`, `hKD`).
* **`DispStabFootLr` [J]** {inv, midReplyFt, midDecOther, midSpec, midRecvSw}: `DispStabFootLk` with
  `midDecReply` replaced by `midReplyFt` (`ReplyXferFt Z H Cs` under the same conditions); **`dispStabFootLk_of_Lr`**,
  top **`kernel_entry_runMcWKR_sysLr`** (globals as `_sysLk`).

Premise honesty: `midReplyFt` speaks of a sub-call of `midDecReply`'s (the transfer inside the Reply decode) and
of every reply object at every `JAtZ` state, not only the looked-up one; it implies `midDecReply` (`midDecReply_of`)
and is **not implied by it**. Not false on reachable states (argument, not proof): `ProjW` is every heap object
word, the kernel-global area and every node word except the other cores' offsets 8 / 32 (their idle thread and
idle SC words, written only at boot); `do_reply_transfer`'s writes are reply / TCB / SC words, the receiver's IPC
buffer frame (in `H`), the executing core's node and, through `possible_switch_to` / the stall of a remote SC,
other cores' scheduling words — none of the excluded ones (P1 `do_reply_transfer.foot` has it in `IpcFoot`; the
missing step is the node identity words, the `KWN ∅ False` walk of goal 2). Removed from the [J] content: the Reply
decode's stable post and `MR` (proved), the restart's footprint.

Named premises: `ReplyXferFt` [J], `DispStabFootLr` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMidDecK
import Fl4Proofs.P3.StPostInv
import Fl4Proofs.P3.XTopJointKEntry41V
import Fl4Proofs.P3.P3KFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- (p3J gen 33) **`TopPostDMXP.mr` from `MachPlatT`** (module docstring). -/
theorem TopPostDMXP.mrT (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDMXP (L := L) X XP σ blk call don m s res) (hR : MR res.2.2 σ.machineState)
    (hq : ∀ inv, DecOut m σ inv → MachT.QInv inv) :
    TopPostDMXP (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) XP σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩
  · refine Or.inl ⟨e, h1, h2, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢; exact ⟨h4, hR⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢
      exact ⟨h4, msF_mrT hM hR ((msF_qperf (hq inv h1) hy).trans (msF_restart h2))⟩

/-- (p3J gen 33) **`TopPostRMX.mr` from `MachPlatT`**. -/
theorem TopPostRMX.mrT (hM : MachPlat arI MR) {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostRMX (L := L) X σ blk call don m ct s res) (hR : MR res.2.2 σ.machineState)
    (hq : ∀ inv, DecOut m σ inv → MachT.QInv inv) :
    TopPostRMX (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩
  · exact Or.inl ⟨e, h1, h2, h3, h4, hR⟩
  · refine Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7, msF_mrT hM hR ?_⟩
    exact ((congrArg Prod.fst (MachT.mtk_specTailG call ct.bv rr σy z hz)).trans
      (msF_qperf (hq inv h3) h5)).trans (msF_restart h4)

/-- (p3J gen 33) **`XCapP.mr` from `MachPlatT`** (module docstring). -/
theorem XCapP.mrT (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      MR r.2.2 σ.machineState ⦄)
    (hq : ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → MachT.QInv inv) :
    XCapP (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) XP s ar σ lbl length slot c blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrT hM h2 hq)
  · exact Or.inr (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrT hM h2 hq)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop)

/-- (p3J gen 33) **`ReplyXferFt` [J]**: `do_reply_transfer`'s footprint after the restart (module docstring). -/
def ReplyXferFt (Z : XSets) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ →
    ∀ ct, sched.cur_thread st s = ok ct → ∀ p, p ∈ Z.R → ∀ (g : Bool) (s1 : S),
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ipc.do_reply_transfer st arI s1 a ct p g ⦃ r => P1.WritesIn st s1 r.1 (Mc.ProjW (L := L) H Cs s1) ⦄

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 33) **The Reply-cap decode leaf of the mid invocation from `ReplyXferFt`** (module docstring). -/
theorem midDecReply_of (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hT : TimeAgree arI)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (hRF : ReplyXferFt (L := L) arI AR Z H Cs) :
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
    refine WP.spec_bind (hRF Z.G V' Ac' Lst' D' s' a' σb J ct hct p hpR g s1 hs1) ?_
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

/-- (p3J gen 33) **`DispStabFootLr` [J]**: `DispStabFootLk` with the Reply-cap decode leaf replaced by
`do_reply_transfer`'s footprint (module docstring). -/
structure DispStabFootLr (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`), verbatim from `DispStabFootLw`. -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- `do_reply_transfer`'s footprint (`ReplyXferFt`), under the mid field's conditions. -/
  midReplyFt : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        ReplyXferFt (L := L) arI AR Z H Cs
  /-- `DispStabFootLk.midDecOther`, verbatim. -/
  midDecOther : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp) Z H Cs s a σ n c
  /-- `DispStabFootLm.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLm.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 33) **`DispStabFootLr → DispStabFootLk`** (module docstring). -/
theorem dispStabFootLk_of_Lr (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLr (L := L) arI AR MR s a σ) :
    DispStabFootLk (L := L) arI AR MR s a σ where
  inv := h.inv
  midDecReply := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    have := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midDecReply_of hA hnd hmax htu hT (MachPlatF.toT hM hIp) hKD hX hct
      (h.midReplyFt hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midDecOther := h.midDecOther
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 33) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLr` only** (`hLr` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLr [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLr : DispStabFootLr (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLk hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLk_of_Lr hA hnd hM hIp hKD hT hmax htu hLr)

end

end Fl4Proofs.P3.Mc
