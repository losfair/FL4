/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g3b, INV-PLAN §4 G3):
**`kernel_entryJ28` = `kernel_entryJ27` without `hNS` / `hNSR`.** Both were
∀-over-states [S] premises (`NativeScope` at every `JHoleAt` / `JAtZR`
state), false for any instance with a `RunningVM` thread (INV-PLAN §3), so
J27 and every top below it were vacuous there. Each consumer now takes
`NativeScope` at its own state, threaded from `SInvB`'s `SInvA.ns` at the
entry state σ by invA's NSK family (spec only, XTopJointKEntry28S):

* the budget check at the `FaultIP` state: `ns_fl4SyscallFaultIP`;
* the dispatch state σb (σb's heap is the `FaultIP` state's): `ns_of_kheap`;
* the preemption hole of an invocation (the `JAtPreMV` state = the spec's
  error outcome of `fl4HandleInvocationR` from σb): `ns_fl4HandleInvocationR`,
  then `hPre_ofZQIMN` (XTopJointMRHole): at the hole itself, and after the
  MCS part (`mcsPPJ*M` posts now carry `NativeScope σ → NativeScope σ'`, from
  `ns_chargeBudget` / `ns_checkBudget` at their spec endpoints) for the
  interrupt (`afterInv_of_mcsIMN`, `handleIrqJIAN`, `JAtZ.signal_atN`);
* every `finish` (after a stopping budget check, after the dispatch, after
  a preemption) starts at a front-end outcome: `ns_front`, then
  `jat_finishJRN` (`jat_finishJRP` at `P := NativeScope`: the fired timers by
  `ns_fl4Awaken`, the activated thread after `schedule` by `ns_schedule`).

The dispatch layer of `kernel_entryJ13PU` (XTopJointKEntry23P) is restated
here with `NativeScope` at the dispatch state (`…N` names: `invoke_afterJMUN`,
`dispatch_invokeJMUN`, `mid_invRecvJMUN`, `dispatch_midJMUN`,
`dispatch_invokeJAllMUN`, `dispatch_all13PUN`, `kernel_entryJ13PUN`), with
`kPreFinHypJI_ofN` and `jat_finishJRN`. NEW TOP `kernel_entryJ28`: J27's
premises minus `hNS` / `hNSR`; nothing added.
-/
import Fl4Proofs.P3.XTopJointKEntry27
import Fl4Proofs.P3.XTopJointKEntry28S
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- **FL4's `finish` from `JAtZR` with `NativeScope` at its own state** (module
docstring): `jat_finishJRP` at `P := NativeScope`: along the fired timers by
`ns_fl4Awaken` (the signal step's `RunningVM` case is then absurd), after
`schedule` by `ns_schedule` (`hvm`). -/
theorem jat_finishJRN {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : NativeScope σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.finish st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), ((), σ1) ∈ (Fl4Spec.fl4Awaken (Z := Unit) σ).1 ∧
      (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) ∧
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ :=
  jat_finishJRP s a σ J hd hnd hAT hVt (fun σ1 => NativeScope σ1)
    (fun σ1 h => SInv.ns_fl4Awaken σ hN ((), σ1) (mem_fl4Awaken_of h))
    (fun _ _ _ _ _ _ _ _ _ _ _ hP _ _ ⟨_, t, tcb, _, hkt, hvm⟩ => absurd hvm (hP t tcb hkt)) hmb
    hA hAN hFO hsni hsend hT hTail hmax htu
    (fun σ1 σ2 _ _ hF hsc _ x hk =>
      SInv.ns_schedule σ1 (SInv.ns_fl4Awaken σ hN ((), σ1) (mem_fl4Awaken_of hF)) ((), σ2)
        (by rw [hsc]; exact Set.mem_singleton _) _ x hk)

/-- **`KPreFinHypJI`**: a `PPQJI` state has `JAt` after the path (`kPreFinHypCI_of`'s first case; no `RestE` premise), with
`NativeScope` at the entry only (g3b): at the front-end outcome by `ns_front`. -/
theorem kPreFinHypJI_ofN {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit}
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS0 : NativeScope σ)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    KPreFinHypJI (L := L) arI AR c σ := by
  intro σ1 hPA r hQ
  obtain ⟨z, hz, Zm, Hm, Csm, Acm, Lstm, Dm, Jm⟩ := hQ
  obtain ⟨σb, ⟨σ0, hF, hb⟩, hy⟩ := hPA
  have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
    mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
  have F := hFin _ hx Zm Hm Csm Acm Lstm Dm r.1 r.2 Jm.toR
  exact WP.spec_mono (jat_finishJRN r.1 r.2 z.2 Jm.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu)
      fun r' ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨z, hz, σ', hmem, hRJ⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
theorem invoke_afterJMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (call bl don : Bool)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 → NativeScope σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar call bl don false (L.mem s (regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => DispPost (L := L) arI AR Q (DispInv call bl don) σ r ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) =
      Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv := by
    rw [← regIdx_cap, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.cap_register
  rw [hcp] at hreg
  have top : ∀ y, y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true call bl don false
      (Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv)).run σ).1 → y ∈ ((DispInv call bl don).run σ).1 :=
    fun y hy => mem_bindE_ok (mem_liftE (ε := Unit) hreg) hy
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind (handle_invocation_entryJMU arI s ar σ J ct hct call bl don false _ hG hE hP hPD hR hVT hVI hN) ?_
  rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, hrel, hX⟩
  rcases hres with ⟨rfl, hy1⟩ | ⟨rfl, hy1⟩
  · show (do
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    refine hok ?_
    exact ⟨y, top y hy, Or.inl ⟨hy1, hrel, ifP_X (fun h => by cases h) hX⟩⟩
  · rw [if_pos rfl] at hX
    refine WP.spec_bind (hPre s1 a1 y.2 hrel hX (SInv.ns_fl4HandleInvocationR true call bl don false _ σ hN y hy)) ?_
    rintro ⟨b, s2, a2⟩ hQ
    refine hok ?_
    exact ⟨y, top y hy, Or.inr ⟨hy1, hQ⟩⟩

set_option maxHeartbeats 4000000 in
theorem dispatch_invokeJMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 → NativeScope σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r => DispPost (L := L) arI AR Q (DispInv call bl don) σ r ⦄ := by
  have h := invoke_afterJMUN arI s ar σ J ct hct call bl don hG hE hP hPD hR hVT hVI hN Q hPre
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  have n65 : fl4_abi.syscall.SysNBSend ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysNBSend fl4_abi.syscall.SysSend; decide
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  rcases hn with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_pos rfl]; exact h
  · rw [if_neg n65, if_pos rfl]; exact h
  · rw [if_neg n15, if_neg n16, if_pos rfl]; exact h


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
theorem mid_invRecvJMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (rg : U64) (sr : Fl4Spec.Register) (cr : Bool)
    (hrg : regIdx sr = rg)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
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
  refine WP.spec_bind (WP.spec_mono (handle_invocation_entryJMU arI s ar σ J ct hct false false true true _ hG hE hP
    hPD hR0 hVT hVI hN)
    fun res h => And.intro (h.toPreMV.mid arI (MidRun.jMidRunHyp_of hW) (J.midEntry hni hE.cnf)) h) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨⟨y1, σm⟩, hy, ⟨hr1, hy1, hM⟩ | ⟨hr1, hy1, hrel, hX⟩⟩, hMV⟩
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
  · dsimp only at hr1
    subst hr1
    obtain ⟨⟨u', σm'⟩, hy', hc', hrel', hX'⟩ := hMV
    have hu' : u' = .error () := by
      rcases hc' with ⟨h1, -⟩ | ⟨-, h2⟩
      · cases h1
      · exact h2
    subst hu'
    rw [if_pos rfl] at hX'
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Err .Preempted)
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    refine WP.spec_bind (hPre_ofZQIMN hARI hA hnd hM hMK hPA hIA hmrt hG.maxTU hG.tu s1 a1 σm' hrel' hX'
      (SInv.ns_fl4HandleInvocationR true false false true true _ σ hN _ hy')) ?_
    rintro ⟨b, s2, a2⟩ ⟨hb, hQ⟩
    dsimp only at hb; subst hb
    show (if false = true then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [if_neg (by decide)]
    exact hok ⟨_, mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_err hy'), Or.inr ⟨rfl, hQ⟩⟩

set_option maxHeartbeats 4000000 in
theorem dispatch_midJMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (c : Fl4Spec.Syscall) (rg : U64)
    (sr : Fl4Spec.Register) (cr : Bool) (hn : MidSysR number c rg sr cr)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have h := mid_invRecvJMUN s ar σ J hni ct hct rg sr cr hn.reg hG hE hP hW hR hPD hR0 hVT hVI hN hARI hA hnd hM hMK hPA hIA hmrt
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
/-- **The invoking dispatches ending in `PPQJI` under `MachPlat`**
(`dispatch_invokeJAll` with mr3's `hPre_ofZQIM`; no `PPPlat`/`IrqPlat`). -/
theorem dispatch_invokeJAllMUN [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ := by
  rw [fl4HandleSyscall_inv hn]
  exact dispatch_invokeJMUN arI s ar σ J ct hct number call bl don hn hG hE hP hPD hR hVT hVI hN _
    fun s1 a1 σ1 h1 h2 h3 => WP.spec_mono (hPre_ofZQIMN hARI hA hnd hM hMK hPA hIA hmrt hG.maxTU hG.tu s1 a1 σ1 h1 h2 h3)
      fun _ h => h.2

set_option maxHeartbeats 4000000 in
/-- **Every native dispatch at `J` under `MachPlat`** (`dispatch_all9M` with
`KDispHyps13PU`; the mid receive leaves narrowed as `KDispHyps15M.to14M` …
`to9M`). -/
theorem dispatch_all13PUN [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps13PU (L := L) arI AR MR Z H Cs D s a σ n c)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP, hPD⟩ := hK.inv _ call bl don hct hi
    exact WP.spec_mono (dispatch_invokeJAllMUN s a σ J _ hct n call bl don hi hG hE hP hPD hR hK.vmt hVI hN hARI
      hA hnd hM hMK hPA hIA hmrt) fun _ h => h.toR
  · obtain ⟨hnq, hvfh⟩ := hK.recv bl cr hr
    exact WP.spec_mono (dispatch_recvJL true hA s a σ J hni hct hnq hvfh n bl cr hr hmax (htu a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · exact WP.spec_mono (dispatch_yieldJ true hA s a σ J hni hct (hmrt a) (hPA.minBudget a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · obtain ⟨rg, sr, cr, hm'⟩ := midSysR_of hm
    obtain ⟨hG, hE, hP, hW, hV, hS6, hPD⟩ := hK.mid _ rg sr cr hct hm'
    obtain ⟨hs, hq⟩ := J.midCQ hni hE
    have hS : JMidRecvHypS (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA _ rg)).bv) cr σ :=
      jMidRecvHypS_of hA (jMidLeavesHyp_of2 hA (jMidLeavesHyp_of3 hA (jMidLeavesHyp_of4 hA hmax htu
        (jMidLeavesHyp_of5 hA hmax htu (jMidLeavesHyp_of6 hA hmax htu hS6)))))
    exact dispatch_midJMUN s a σ J hni _ hct n c rg sr cr hm' hG hE hP hW.toP
      (jMidRecvHyp_of hA hG.maxTU hG.tu hs hq hW hV hS) hPD hR hK.vmt hVI hN hARI hA hnd hM hMK hPA hIA hmrt


set_option maxHeartbeats 16000000 in
/-- **`kernel_entryJ13PB` on `KDispHyps13PU`** (module docstring). -/
theorem kernel_entryJ13PUN [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps13PU (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hPF := kPreFinHypJI_ofN hFin hA hnd hmb hNS0 hT hmax htu
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
    exact JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF) hAK hA
      hnd hmrt hmb hmax htu
  refine WP.spec_bind (WP.spec_and hBud (budget_ok_mr hM hMK hA hR _)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨hTr, hFa⟩, hMRb⟩
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
    exact WP.spec_mono (jat_finishJRN s2 a1 σb J'.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
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
    obtain ⟨hMRσb, hVIσb⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _)
      hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    have hNSb : NativeScope σb := SInvN.ns_of_kheap ekh (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF)
    refine WP.spec_bind (dispatch_all13PUN s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hMRσb hVIσb hNSb hARI hA hnd hM hMK hPA hIA hmrt hmax htu) ?_
    rintro ⟨s3, a2⟩ ⟨y, hy, ⟨hy1, hR, hJ⟩ | ⟨hy1, hQ⟩⟩
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2 JmR
      exact WP.spec_mono (jat_finishJRN s3 a2 σm JmR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
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

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ27` without `hNS` / `hNSR`** (module docstring): every
`NativeScope` the proof needs is at a state the path reaches, from SInvB's
`SInvA.ns` at the entry state. Premises as J27 otherwise. -/
theorem kernel_entryJ28 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV27 (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR27 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hct : σ.curThread ≠ σ.idleThread := hni.1
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  exact kernel_entryJ13PUN s a σ J hni hR hS.1.1.vim hS.1.1.ns n c hn hflag
    (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      ((((hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to26 hnd hS hni hQ hB hBA).to25 hA hmax htu hmb J'
        (hBA.enteredP hnd hni)).to23 hA hmax htu).to13PU J' hBA hA hnd hM hKD hmax htu)
    (fun x hx Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' J').toR (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
    hARI hA hnd hM hKD.toK hPA hIA hmrt hmb hT hmax htu

end

end

end Fl4Proofs.P3
