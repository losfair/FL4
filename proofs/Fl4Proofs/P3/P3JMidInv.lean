/-
P3 (p3J gen 32, finished gen 33): **the mid class's invocation half reduced to its per-cap decode leaf** (the stable invoke skeleton
for ReplyRecv / NBSendRecv / NBSendWait, with footprint).

`handle_invocation false false true true cptr` is XTopJointEntry's `handle_invocation_refinesMXP` (generic in the
posts `X`, `XP`), here at

* **`MidX Z H Cs MR s0`** := `JStab Z H Cs ∧ MR ∧` the run from `s0` writes only `ProjW H Cs s0`;
* **`MidXP Z H Cs MR s0`** := the footprint from `s0`, and FL4's `after_invocation … (Err Preempted)` from there
  ends with `false` at an outcome of `preemptionPath` with `JStab Z H Cs`, `MR` and footprint `ProjW H Cs s0`
  (exactly P3JMidCls's `MidInvPost` preempted half).

Its leaves at a dispatch state `J : JAtZ (Z.mv Z.G V') H Cs` are proved here except the decode of the looked-up cap:
the front reads (`JAtZ.frontEx`), the extra caps (`JAtZ.extraJ`; their fault needs nothing since `blocking =
false`), the lookup fault (likewise), the error reply (`is_call = false`: nothing happens), the success tail
(StPostInv's `JAtZ.flTailJStF`, `MKD.fl_tail`, and its footprint **`flTailProjW`**: the state read and P2's
`set_thread_state.kwN` at `Kp = ∅`, `Nd = False` into `ProjW` by P3JMcKwN's `kwN_projW`, **`stsProjW`**), the
current thread kept (`perfCurKeep`, as StPostInv's `handle_invocation_replyJSt`: **`midPK`**); the tail at `MidX`
is **`midTailSt`**, the post conversion **`midInvPost_of`**.

* **`MidDecSt` [J]**: at every dispatch state of the entry (as `MidInvStFt`), for the front reads and every slot
  `sl` / cap `c` the lookup can find (`JPathAtMU44w`'s binder chain without its `NativeCap` / `LookAt` / `W`
  antecedents), the decode leaf `XCapP (MidX …) (MidXP …)` of `c` at `is_call = blocking = false`,
  `can_donate = first_phase = true`.
* **`midInvHI`** (gen 33): the invocation at `MidX` / `MidXP` by `handle_invocation_refinesMXP` with every premise
  a separate `?_` goal (StPostInv's `handle_invocation_replyJSt` shape). Gen 32's version (`have hH := …` with the
  whole application elaborated at once, then `spec_mono`) hit a `whnf` timeout at 8M heartbeats: `diagnostics` showed
  the unifier unfolding `XCapP` into the spec decode (`specDec`, `invocationType`, `archDecodeIrqControlInvocation`,
  `List.map` / `List.length` `f a =?= f b` heuristics ~10^6); in the `refine` shape each premise is checked against
  its instantiated type and the file elaborates in seconds.
* **`midInvStFt_of`**: `MidDecSt → MidInvStFt`.
* **`DispStabFootLd` [J]** {inv, midDec, midSpec, midRecvSw} (P3JMidCls's `DispStabFootLm` with `midDec` for
  `midInv`), **`dispStabFootLm_of_Ld`**, top **`kernel_entry_runMcWKR_sysLd`** (globals as `_sysLm`).

Narrowing honesty: `midDec` speaks of a sub-call of `midInv`'s call (the decode and perform of the looked-up cap
inside `handle_invocation`); it implies `midInv` (`midInvStFt_of`) and is not implied by it. Justification that it
is not false on reachable states: it is `midInv` with the proved skeleton removed — the decode leaves are where the
non-stable chain's per-cap premises sit (`JPathMEU44`, all `True` but K1/K3/K4/K6/K7; the non-stable decode
leaves `decOK_JMM` etc. build their exits at `Z.mv G' V'` with the entry's `H`/`Cs` except retypes, which `CKI`
excludes: no untyped cap is in any slot); the footprint of every non-retype decode is in `ProjW`. Removed from the
[J] content: the front reads, the lookup, the extra-cap lookup, the success tail and the error reply of the mid
class's invocation.

Named premises: `MidDecSt` [J], `DispStabFootLd` [J] (above). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMidCls
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 32) **The unpreempted post of the mid invocation** (module docstring). -/
def MidX (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s0 : S) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) : Prop :=
  JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧ MR a1 σ1.machineState ∧ P1.WritesIn st s0 s1 (Mc.ProjW (L := L) H Cs s0)

/-- (p3J gen 32) **The preempted post of the mid invocation** (module docstring). -/
def MidXP (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s0 : S) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) : Prop :=
  P1.WritesIn st s0 s1 (Mc.ProjW (L := L) H Cs s0) ∧
  syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => r.1 = false ∧
    (∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1,
      JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 z.2 ∧ MR r.2.2 z.2.machineState) ∧
    P1.WritesIn st s0 r.2.1 (Mc.ProjW (L := L) H Cs s0) ⦄

/-- (p3J gen 32) **`MidDecSt` [J]**: the decode leaf of the mid invocation at every dispatch state of the entry
(module docstring). -/
def MidDecSt (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct rg sr cr, sched.cur_thread st s' = ok ct → MidSysR n c rg sr cr →
    ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
      msg.msg_info st s' ct = ok info →
      Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False) →
      msg.lookup_ipc_buffer st s' false ct = ok buf →
      Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False) →
      ipc.lookup_extra_caps st s' ct buf info = ok r2 →
      (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False) →
      Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False) →
      ∀ (sl : Fl4Spec.CslotPtr) (cp : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
        (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
        capAt (L.mem s') (cslotAddr sl) = ok cp → Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap cp, σb)}, False) →
        r2 = .Ok e → er = .ok exs →
        XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
          info.label (msgLen info buf) (cslotAddr sl) cp false false true true buf e mi.miLabel
          (argsU.map UScalar.bv) (Fl4Spec.toBl (L.mem s' (regA ct rg)).bv) sl exs buffer ct

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 32) **`set_thread_state` of a thread of `Z.T` writes only `ProjW`** (module docstring). -/
theorem stsProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (v : U64) :
    sched.set_thread_state st s t v ⦃ s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨⟨Q0, R0, h0⟩, -⟩ := J.blk
  exact WP.spec_mono (P1.sched.set_thread_state.kwN (Kp := ∅) (Nd := False) (Sg := P1.Heap.frame H)
    (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) (Es := P1.EH H) s t v h0 (J.zH.1 t ht)
    (Set.notMem_empty t)) fun s' f => (P1.WritesA.w f).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

/-- (p3J gen 32) **The non-call success tail writes only `ProjW`** (module docstring). -/
theorem flTailProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) :
    flTail (st := st) t false s a ⦃ res => P1.WritesIn st s res.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  unfold flTail
  refine WP.spec_bind (P0.obj.Tcb.state.p0 st t s L.total) fun i _ => ?_
  split
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact WP.spec_bind (stsProjW J ht _) fun s3 h3 => (WP.spec_ok _).2 h3
  · exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)

variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 32) **The success tail at `MidX`** (module docstring). -/
theorem midTailSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s0 : S}
    {ct : U64} (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit) (hX : MidX (L := L) arI AR MR Z H Cs s0 s1 a1 σ')
    (hc : σ'.curThread = ct.bv) :
    flTail (st := st) ct false s1 a1 ⦃ res => res.1 = .Ok () ∧
      ∃ z ∈ (specTail false ct.bv [] σ').1, RelTopM (L := L) res.2.1 z.2 ∧
        MidX (L := L) arI AR MR Z H Cs s0 res.2.1 res.2.2 z.2 ⦄ := by
  obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J'⟩, hR', hW1⟩ := hX
  have hct' : ct ∈ (Z.mv G1 V1).T := TopSR.cur_mem J'.xtop.fin.1 hc.symm
  refine WP.spec_mono (WP.spec_and (WP.spec_and (J'.flTailJStF hc) (MKD.fl_tail L.total hA hKD hR'))
    (flTailProjW J' hct')) ?_
  rintro res ⟨⟨⟨h1, z, hz, h2, h3⟩, h4⟩, h5⟩
  exact ⟨h1, z, hz, h2, JStab.mv h3, msF_mrT hMT h4 (congrArg Prod.fst (MachT.mtk_specTailG _ _ _ σ' z hz)),
    hW1.projW_trans h5⟩

/-- (p3J gen 32) **The invocation keeps the current thread** (as `handle_invocation_replyJSt`). -/
theorem midPK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (hcur : σ.curThread = ct.bv) (blocking is_call can_donate : Bool) :
    ∀ inv σ1 y, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blocking is_call can_donate inv).run σ1).1 →
      y.2.curThread = ct.bv := by
  intro inv σ1 y hst hy
  rw [perfCurKeep _ _ _ inv σ1 y hy]
  obtain ⟨x, hk⟩ := (J.xtop.curTcb hcur).2
  rw [hcur] at hst
  have hm : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
    rw [hst]; exact Set.mem_singleton _
  rw [Notif.setThreadState_eq .restart hk] at hm
  have e : σ1 = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
  rw [e, Sched.stsAct_rec]; exact hcur

/-- (p3J gen 32) `HIPostMXP` at `MidX` / `MidXP` is `MidInvPost`. -/
theorem midInvPost_of {s0 : S} {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : HIPostMXP (L := L) (MidX (L := L) arI AR MR Z H Cs s0) (MidXP (L := L) arI AR MR Z H Cs s0) true σ
      false false true true cptr res) :
    Mc.MidInvPost (L := L) arI AR MR Z H Cs cptr σ s0 res := by
  obtain ⟨y, hy, hc, -, hXr⟩ := h
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_neg (by rw [h1]; intro e; cases e)] at hXr
    exact ⟨hXr.2.2, y, hy, Or.inl ⟨h1, h2, hXr.1, hXr.2.1⟩⟩
  · rw [if_pos h1] at hXr
    refine ⟨hXr.1, y, hy, Or.inr ⟨h2, ?_⟩⟩
    rw [h1]; exact hXr.2

set_option maxHeartbeats 2000000 in
/-- (p3J gen 33) **The mid invocation at `MidX` / `MidXP`** (module docstring): `handle_invocation_refinesMXP` in
the `refine … ?_` shape, every premise a separate goal. -/
theorem midInvHI [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (hD : MidDecSt (L := L) arI AR MR Z H Cs s a σ n c) (σb : Fl4Spec.State Unit) (hBA : BudgetAt σ σb true)
    (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
    (hKF : KFrontB (L := L) arI s a s' a') (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb)
    (hMb : MR a' σb.machineState) (hCb : SInvCk.CKI σb) (hRRb : SInvRr.RR σb)
    (ct rg : U64) (sr : Fl4Spec.Register) (cr : Bool) (hct : sched.cur_thread st s' = ok ct) (hn : MidSysR n c rg sr cr) :
    syscall.handle_invocation st arI s' a' false false true true (L.mem s' (Endp.regA ct rg)) ⦃ res =>
      HIPostMXP (L := L) (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') true σb
        false false true true (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hX := J.xtop
  refine handle_invocation_refinesMXP arI (MidX (L := L) arI AR MR Z H Cs s')
    (MidXP (L := L) arI AR MR Z H Cs s') true s' a' σb
    Z.th Z.G hX.rel.1 hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 hX.rel.2.2.2.2.1 ?x0 ct hct hcur htcb
    false false true true (L.mem s' (Endp.regA ct rg)) info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her ?rr
    (argsU.map UScalar.bv) hmrs ?fl ?repS ?repF ?pk ?dec
  case x0 => exact ⟨JStab.mv J.stab, hMb, P1.WritesIn.refl _ _⟩
  case rr =>
    exact (J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her).imp id
      fun ⟨f, f', h1, h2, _⟩ => ⟨f, f', h1, h2, fun h => by cases h⟩
  case fl => exact fun h => by cases h
  case repS => exact fun s1 a1 σ' _ hXs hc => midTailSt hA hMT hKD s1 a1 σ' hXs hc
  case repF =>
    intro a1 e e' hX1 _
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 ⟨rfl, ((), σb), mem_whenP (fun h => h.elim) (fun _ => rfl), hX.relTop, hX1⟩
  case pk => exact midPK J hcur false false true
  case dec =>
    intro sl cp e exs hsl hc hget he hexs
    have hd := hD σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      hinfo hmi hbuf hbuffer hr2 her hmrs sl cp e exs hsl hc hget he hexs
    exact hd

set_option maxHeartbeats 2000000 in
/-- (p3J gen 33) **`MidDecSt → MidInvStFt`** (module docstring): `midInvHI` and `midInvPost_of`. -/
theorem midInvStFt_of [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (hD : MidDecSt (L := L) arI AR MR Z H Cs s a σ n c) : Mc.MidInvStFt (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn
  exact WP.spec_mono (midInvHI hA hMT hKD hD σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn)
    fun res h => midInvPost_of h

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

/-- (p3J gen 32) **`DispStabFootLd` [J]**: `DispStabFootLm` with the mid invocation reduced to its decode leaf
(module docstring). -/
structure DispStabFootLd (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`), verbatim from `DispStabFootLw`. -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- The mid invocation's decode leaf (`MidDecSt`), under the mid field's conditions. -/
  midDec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecSt (L := L) arI AR MR Z H Cs s a σ n c
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

/-- (p3J gen 32) **`DispStabFootLd → DispStabFootLm`** (module docstring). -/
theorem dispStabFootLm_of_Ld [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLd (L := L) arI AR MR s a σ) : DispStabFootLm (L := L) arI AR MR s a σ where
  inv := h.inv
  midInv := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    haveI := hV
    exact midInvStFt_of hA (MachPlatF.toT hM hIp) hKD (h.midDec hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 32) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLd` only** (`hLd` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLd [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLd : DispStabFootLd (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLm hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLm_of_Ld hA hM hIp hKD hLd)

end

end Fl4Proofs.P3.Mc
