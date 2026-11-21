/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch13): **`kernel_entryJ8`: the
ReplyRecv / NBSendRecv / NBSendWait dispatch shell proved, the preemption path
without named premises, `KPreFinRestHypI` gone.**

* `MidSysR`: the three numbers with FL4's cap register, the spec's register
  and the receive's can-reply flag; `fl4HandleSyscall_mid` (the spec branch:
  the register read, `fl4HandleInvocationR true false false true true`, then
  `withoutPreemption (handleRecv true cr)`).
* `JMidRecvHyp` [W] (narrows `KDispHypsRI.mid`, which named the whole
  dispatch): only the receive after a successful first phase, at a `JMid`
  state (l4v `invs and ct_active`) that is an `.ok` outcome of the invocation
  from the dispatch state (on the path, not ∀ states). l4v
  `handle_recv_corres` at the mid state (`handleReplyRecv`'s second half).
  Removal: sch12 (2) (i)–(iii) (hnq/hvfh at the mid state by a frame, the
  receive leaves from `MidE` without `Entered`, the blocking leaves ending in
  `JAtZR` under a pending switch).
* `mid_invRecvJ` / `dispatch_midJ`: `handle_invocation_entryJ` with
  `HIPostMXP.mid` (`JMidPerfHyp` [W] as sch12, `MidEntry` from `Entered` and
  `JEntryAt.cnf` at the dispatch state, i.e. the entry's own [J] fact),
  `after_invocation`: `Ok` → the receive (`JMidRecvHyp`), `Err` → the
  preemption path (`hPre_ofZQI`, ending in `PPQJI`).
* `KDispHyps8` (`inv`, `recv` as before; `mid`: the entry facts JEntryGlob /
  JEntryAt / JPathAt for the mid invocation's flags and cap register, as
  `inv` has them, plus `JMidPerfHyp` and `JMidRecvHyp`), `dispatch_all8`
  (every dispatch ends in `DispPostR` with `PPQJI`), `kPreFinHypJI_of`
  (finish after every preempted dispatch: `PPQJI` has `JAt` after the path,
  so no `RestE` premise), `kernel_entryJ8` = `kernel_entryJ7` with `IrqPlat`
  for `IrqPlatI` (XTopJointIrqPlat), no `hRest` (kp17), no `hPR`
  (`KPreFinRestHypI` deleted: kp17's `RestE` holes end in `PPQJI`,
  XTopJointIrqZJ), `KDispHyps8` for `KDispHypsRI`.
-/
import Fl4Proofs.P3.XTopJointIrqZJ
import Fl4Proofs.P3.XTopJointMidRunS
import Fl4Proofs.P3.XTopJointKEntry7
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- ReplyRecv / NBSendRecv / NBSendWait with FL4's cap register `rg`, the
spec's register `sr` and the receive's can-reply flag `cr`. -/
def MidSysR (n : I64) (c : Fl4Spec.Syscall) (rg : U64) (sr : Fl4Spec.Register) (cr : Bool) : Prop :=
  (n = fl4_abi.syscall.SysReplyRecv ∧ c = .sysReplyRecv ∧ rg = layout.reg.REPLY ∧
    sr = Fl4Spec.replyRegister ∧ cr = true) ∨
  (n = fl4_abi.syscall.SysNBSendRecv ∧ c = .sysNBSendRecv ∧ rg = layout.reg.NBSEND_RECV_DEST ∧
    sr = Fl4Spec.nbsendRecvDest ∧ cr = true) ∨
  (n = fl4_abi.syscall.SysNBSendWait ∧ c = .sysNBSendWait ∧ rg = layout.reg.REPLY ∧
    sr = Fl4Spec.replyRegister ∧ cr = false)

theorem midSysR_of {n : I64} {c : Fl4Spec.Syscall} (h : MidSys n c) : ∃ rg sr cr, MidSysR n c rg sr cr := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, _, _, Or.inl ⟨h1, h2, rfl, rfl, rfl⟩⟩
  · exact ⟨_, _, _, Or.inr (Or.inl ⟨h1, h2, rfl, rfl, rfl⟩)⟩
  · exact ⟨_, _, _, Or.inr (Or.inr ⟨h1, h2, rfl, rfl, rfl⟩)⟩

theorem regIdx_nbsendRecvDest : regIdx Fl4Spec.nbsendRecvDest = layout.reg.NBSEND_RECV_DEST := by
  unfold layout.reg.NBSEND_RECV_DEST layout.reg.R13; rfl

theorem MidSysR.reg {n : I64} {c : Fl4Spec.Syscall} {rg : U64} {sr : Fl4Spec.Register} {cr : Bool}
    (h : MidSysR n c rg sr cr) : regIdx sr = rg := by
  rcases h with ⟨-, -, rfl, rfl, -⟩ | ⟨-, -, rfl, rfl, -⟩ | ⟨-, -, rfl, rfl, -⟩
  · exact regIdx_reply
  · exact regIdx_nbsendRecvDest
  · exact regIdx_reply

/-- The spec's mid syscall branch (`fl4HandleSyscall true`). -/
def DispMid (sr : Fl4Spec.Register) (cr : Bool) : Fl4Spec.PMonad Unit Unit := do
  let cptr ← Fl4Spec.withoutPreemption <| Fl4Spec.getCapReg (Z := Unit) sr
  Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr
  Fl4Spec.withoutPreemption <| Fl4Spec.handleRecv (Z := Unit) true cr

theorem fl4HandleSyscall_mid {n : I64} {c : Fl4Spec.Syscall} {rg : U64} {sr : Fl4Spec.Register} {cr : Bool}
    (h : MidSysR n c rg sr cr) : Fl4Spec.fl4HandleSyscall (Z := Unit) true c = DispMid sr cr := by
  rcases h with ⟨-, rfl, -, rfl, rfl⟩ | ⟨-, rfl, -, rfl, rfl⟩ | ⟨-, rfl, -, rfl, rfl⟩ <;> rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[W] The receive at the mid state** (module docstring): every `.ok`
outcome of the first-phase invocation from `σ`, at every `JMid` FL4 state
related to it. -/
def JMidRecvHyp (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (cr : Bool) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    ∀ (s1 : S) (a1 : A), JMid (L := L) arI AR s1 a1 y.2 →
      syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr y.2).1,
        RelTopM (L := L) r.1 z.2 ∧ ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
          JAtZR (L := L) arI AR Z H Cs Ac Lst D r.1 r.2 z.2 ⦄

/-- **The dispatch premises with the mid syscalls' entry facts** (module
docstring): `inv`, `recv` as `KDispHypsRI`; `mid`: JEntryGlob / JEntryAt /
JPathAt for the mid invocation (the [J] entry facts `inv` has), the perform
[W] `JMidPerfHyp` (sch12) and the receive [W] `JMidRecvHyp`. -/
structure KDispHyps8 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ

/-- `finish` after a preempted dispatch from a `PPQJI` state. -/
def KPreFinHypJI (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ σ1, PreemptedAt c σ σ1 → ∀ r : S × A, PPQJI (L := L) arI AR σ1 r →
    syscall.finish st arI r.1 r.2 ⦃ r' => (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨
      ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, ∃ σ',
        ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) z.2).1 ∧
        RJ (L := L) arI AR r'.1 r'.2 σ' ⦄

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The mid syscalls' invocation, `after_invocation` and receive at `J`**
(module docstring). -/
theorem mid_invRecvJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (rg : U64) (sr : Fl4Spec.Register) (cr : Bool)
    (hrg : regIdx sr = rg)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct rg))
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (DispMid sr cr) σ r ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs sr) =
      Fl4Spec.toBl (L.mem s (regA ct rg)).bv := by
    rw [← hrg, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' sr
  rw [hcp] at hreg
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind (WP.spec_mono (handle_invocation_entryJ arI s ar σ J ct hct false false true true _ hG hE hP)
    fun res h => h.mid arI (MidRun.jMidRunHyp_of hW) (J.midEntry hni hE.cnf)) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨y1, σm⟩, hy, ⟨hr1, hy1, hM⟩ | ⟨hr1, hy1, hrel, hX⟩⟩
  · dsimp only at hr1 hy1 hM
    subst hr1 hy1
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    show (if true = true then syscall.handle_recv st arI s1 a1 true cr else ok (s1, a1)) ⦃ _ ⦄
    rw [if_pos rfl]
    refine WP.spec_mono (hR _ hy rfl s1 a1 hM) ?_
    rintro r ⟨z, hz, hrl, hJ⟩
    exact ⟨(.ok z.1, z.2), mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_ok hy (mem_liftE hz)),
      Or.inl ⟨rfl, hrl, hJ⟩⟩
  · dsimp only at hr1 hy1 hrel hX
    subst hr1 hy1
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Err .Preempted)
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    refine WP.spec_bind (hPre_ofZQI hARI hA hnd hPP hmrt hIP hNS hG.maxTU hG.tu s1 a1 σm hrel hX) ?_
    rintro ⟨b, s2, a2⟩ ⟨hb, hQ⟩
    dsimp only at hb; subst hb
    show (if false = true then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [if_neg (by decide)]
    exact hok ⟨_, mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_err hy), Or.inr ⟨rfl, hQ⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`dispatch_syscall` for ReplyRecv / NBSendRecv / NBSendWait at `J`**
(module docstring), against `fl4HandleSyscall true`'s branch. -/
theorem dispatch_midJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (c : Fl4Spec.Syscall) (rg : U64)
    (sr : Fl4Spec.Register) (cr : Bool) (hn : MidSysR number c rg sr cr)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have h := mid_invRecvJ s ar σ J hni ct hct rg sr cr hn.reg hG hE hP hW hR hARI hA hnd hPP hmrt hIP hNS
  rw [fl4HandleSyscall_mid hn]
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 rfl
  rcases hn with ⟨rfl, -, rfl, -, rfl⟩ | ⟨rfl, -, rfl, -, rfl⟩ | ⟨rfl, -, rfl, -, rfl⟩
  · rw [if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBWait; decide), if_pos rfl]
    exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBWait; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysReplyRecv; decide), if_pos rfl]
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NBSEND_RECV_DEST) ?_
    rintro c2 rfl
    exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBWait; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysReplyRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBSendRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBSendRecv; decide), if_pos rfl]
    exact h

set_option maxHeartbeats 4000000 in
/-- **Every native dispatch at `J` ending in `DispPostR` with `PPQJI`** (module docstring). -/
theorem dispatch_all8 [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps8 (L := L) arI AR Z H Cs D s a σ n c)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP⟩ := hK.inv _ call bl don hct hi
    exact WP.spec_mono (dispatch_invokeJAll s a σ J _ hct n call bl don hi hG hE hP hARI hA hnd hPP hmrt hIP hNS)
      fun _ h => h.toR
  · obtain ⟨hnq, hvfh⟩ := hK.recv bl cr hr
    exact WP.spec_mono (dispatch_recvJL true hA s a σ J hni hct hnq hvfh n bl cr hr hmax (htu a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · exact WP.spec_mono (dispatch_yieldJ true hA s a σ J hni hct (hmrt a) (hmb a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · obtain ⟨rg, sr, cr, hm'⟩ := midSysR_of hm
    obtain ⟨hG, hE, hP, hW, hR⟩ := hK.mid _ rg sr cr hct hm'
    exact dispatch_midJ s a σ J hni _ hct n c rg sr cr hm' hG hE hP hW hR hARI hA hnd hPP hmrt hIP hNS


/-- **`KPreFinHypJI`**: a `PPQJI` state has `JAt` after the path (`kPreFinHypCI_of`'s first case; no `RestE` premise). -/
theorem kPreFinHypJI_of {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit}
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    KPreFinHypJI (L := L) arI AR c σ := by
  intro σ1 hPA r hQ
  obtain ⟨z, hz, Zm, Hm, Csm, Acm, Lstm, Dm, Jm⟩ := hQ
  obtain ⟨σb, ⟨σ0, hF, hb⟩, hy⟩ := hPA
  have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
    mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
  have F := hFin _ hx Zm Hm Csm Acm Lstm Dm r.1 r.2 Jm.toR
  exact WP.spec_mono (jat_finishJR r.1 r.2 z.2 Jm.toR F.hd hnd hA F.vt (signalRestJHypZR_of_ns hNSR Hm Csm) hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu (hvm_of_ns hNS))
      fun r' ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨z, hz, σ', hmem, hRJ⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ7`
with `IrqPlat` for `IrqPlatI`, no `JPreemptRestHypE` (kp17) and no
`KPreFinRestHypI` (every preemption hole ends in `PPQJI`), `KDispHyps8`
(mid: entry facts, `JMidPerfHyp` [W], `JMidRecvHyp` [W]) for `KDispHypsRI`
(module docstring). -/
theorem kernel_entryJ8 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps8 (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hPF := kPreFinHypJI_of hFin hA hnd hmb hNS hNSR hT hmax htu
  have hvm := hvm_of_ns hNS
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  -- the FaultIP write
  unfold syscall.handle_syscall_old
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx hnx
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBu := hB x hk'
  -- the trap flag and the number range
  refine WP.spec_bind (hflag ct v hct) ?_
  rintro f hf
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hn.range.1, if_neg hn.range.2]
  -- budget_ok
  have hAK := hARI.toARKeep
  have hBud : syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart)
          (faultIPSt σ σ.curThread x) = ({(true, σ')}, False) ∧
        σ'.kheap = (faultIPSt σ σ.curThread x).kheap ∧ σ'.curThread = (faultIPSt σ σ.curThread x).curThread ∧
        σ'.curSc = (faultIPSt σ σ.curThread x).curSc ∧
        σ'.schedulerAction = (faultIPSt σ σ.curThread x).schedulerAction ∧
        σ'.idleThread = (faultIPSt σ σ.curThread x).idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget (faultIPSt σ σ.curThread x)).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2) ⦄ := by
    rcases hBu.tmo with hnt | ⟨hnq, xt, hkt, hrr, p, bd, rr, hth, hper, hcb⟩
    · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkF hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnt)) fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
          obtain ⟨σ', he, Ac', Lst', D', J'⟩ := h2 hf
          refine ⟨(false, σ'), ?_, rfl, _, Ac', Lst', D', J'⟩
          unfold specBudget faultIPSt
          rw [he]; exact Set.mem_singleton _⟩
    · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkT hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnq hkt hrr hth hper hcb)) fun r ⟨h1, h2⟩ =>
          ⟨h1, fun hf => by
            obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
            exact ⟨z, hz, hz1, _, Ac', Lst', D', J'⟩⟩
  refine WP.spec_bind hBud ?_
  rintro ⟨b, s2, a1⟩ ⟨hTr, hFa⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J'⟩ := hFa rfl
    obtain ⟨b', σb⟩ := z
    simp only at hz1; subst hz1
    show (do
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPost (L := L) arI AR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1 J'.toR
    exact WP.spec_mono (jat_finishJR s2 a1 σb J'.toR F.hd hnd hA F.vt (signalRestJHypZR_of_ns hNSR H Cs) hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPost (L := L) arI AR c σ r ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    refine WP.spec_bind (dispatch_all8 s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hARI hA hnd hPP hmrt hmb hIP hNS hmax htu) ?_
    rintro ⟨s3, a2⟩ ⟨y, hy, ⟨hy1, hR, hJ⟩ | ⟨hy1, hQ⟩⟩
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2 JmR
      exact WP.spec_mono (jat_finishJR s3 a2 σm JmR F.hd hnd hA F.vt (signalRestJHypZR_of_ns hNSR Hm Csm) hmb
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (hPF σ1 hPA (s3, a2) hQ) ?_
      rintro r (hfail | ⟨z, hz, σ', hmem, hRJ⟩)
      · exact Or.inl (fail_kentry hF hb hy hfail)
      · have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
          mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
        exact Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩


end

end

end Fl4Proofs.P3
