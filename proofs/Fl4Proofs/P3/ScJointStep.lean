/-
P3 (DESIGN.md §9), scheduling contexts: **the SC family's step on `JAt`**
(the first family-level preservation theorem): `JAtZ` before the decode of
an SC cap ⇒ `XTop` and `JAtZ` after (`sched_controlJ_step`).

From the producer's post: `XTopAt` (`xtop_sc_step`), the scheduler and
notification relations, `NSC`, `Inv` (`decode_configure_refines`), the call
stacks, yield, MCP and reply placement (`ScAll.of_k`), `BlockedScActive`
(`bsa_configure`, the decoded `REFILL_MAX` from `retP_configureDec`); the
fields no SC step touches by `JAtZ.sc_frame`; `CurRun` (`curRun_sc_step`);
the buffer words, slots apart, `JPlaced`, `JKern`, the untyped caps' facts
and `JCovD` (ScJointRest: `JAtZ.sc_buf`, `sc_apart`, `sc_jpl`, `sc_kern`,
`sc_utc`, `sc_jcov`; the current SC kept by `FK`, ScFieldKeep). The dead
set: the step cuts links only (ScLinkKeep) outside Bind's SC and new thread
or notification, so the dead stay dead (`deadP_sc_step`); Bind's pair leaves
the dead set, covered by its caps (`cover_cap`: the invoked SC cap's slot,
the extra cap's slot; premises `hslot`, `hslotS`, `hsb`, `hssz`, `hx0S`, the
decode site's cap lookup and `valid_cap`).

The mid-entry facts (`CurInv` unless a reschedule is pending, `CurOwn`
under one, `OffOK`, `ActIdle`): the restart keeps them (`restart_mid`; the
entry action `resume_cur_thread`, premise `hres`), and the invocation is a
`MidK` step (ScMidKeep: Bind, UnbindObject, YieldTo, the decodes'
checks `rdp_decode*Pre` and `hback` placing the SC's thread off the current
and idle ones) or, for Configure of an SC other than the current one, a
`MidKn` step (its `possible_switch_to`; `ActIdle` then from
`decode_configure_refinesA`, premise `hpi`).

Configure of the current SC (bound to the current thread) is a `MidKW` step
ending with the consumed time cleared and a reschedule pending
(`mkw_configureCur`, ScMidCur), hence `MidA`.

Named per-op premise (`hRest`, at the decode's post, over its spec run,
`ScStepP1`): P1-supplied, the node-0 `DEBUG_TCBS` word kept and `BlkOK`.

`sched_controlJ_step` also returns the spec run it follows (unchanged state
with the spec's decode failing, or the decode, restart and Configure
outcomes), so `decode_invocation_sched_controlJ` joins it with
`decode_invocation_sched_controlJAt`'s outcome (each spec step
single-valued): `XCap` at `JAt` for the SchedControl cap.
-/
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScBsaOps
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.ScMidKeep
import Fl4Proofs.P3.ScMidCur
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The P1-supplied part of an SC step** (the node-0 `DEBUG_TCBS` word kept,
every debug word kept — KENTRY-PLAN g2i, for `JAtZ.live`; an SC decode writes
no TCB debug link and no debug head —, `BlkOK` after). -/
def ScStepP1 (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s s' : S) : Prop :=
  ∃ (Ac' : Set U64),
    L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∧
    P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' ∧
    P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s'

theorem retP_bind_never {α β : Type} {P : β → Prop} {m : Fl4Spec.SEMonad Unit α} {f : α → Fl4Spec.SEMonad Unit β}
    (hm : RetP (fun _ => False) m) : RetP P (m >>= f) := by
  intro σ x hx v hv
  rw [ExceptT.run_bind] at hx
  obtain ⟨⟨e, σ'⟩, he, hx⟩ := hx
  cases e with
  | error e => rw [Set.mem_singleton_iff.1 hx] at hv; cases hv
  | ok a => exact (hm σ _ he a rfl).elim

/-- Bind's decoded cap is the first extra cap. -/
theorem retP_bindHead (sc : Fl4Spec.ObjRef) (excaps : List Fl4Spec.Cap) :
    RetP (fun v => ∃ a rest, excaps = a :: rest ∧ v = .invokeSchedContextBind sc a)
      (Fl4Spec.decodeSchedContextBind (Z := Unit) sc excaps) := by
  unfold Fl4Spec.decodeSchedContextBind
  cases excaps with
  | nil =>
    refine retP_bind_never ?_
    unfold Fl4Spec.NonDetE.whenE; rw [if_pos List.length_nil]; exact retP_throw _
  | cons a rest =>
    refine retP_bind _ fun _ => ?_
    rw [retOk_bind]
    simp only [List.head?_cons]
    repeat (first | exact retP_pure ⟨_, _, rfl, rfl⟩ | exact retP_throw _ | (refine retP_bind _ fun _ => ?_) | split | (dsimp only))

/-- **`CurRun` after an SC step**: the restart makes the current thread
runnable, and the invocation (`ScTKw (·=False)`) keeps every TCB state and
the current thread. -/
theorem curRun_sc_step {σ σ0 σ' : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hkc : σ.kheap t = some (.tcb x)) (hct : σ.curThread = t)
    (he0 : Fl4Spec.setThreadState (Z := Unit) t .restart σ = ({((), σ0)}, False))
    (hK1 : ScTKw (fun _ => False) σ0 σ') : CurRun σ' := by
  have hσ0 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he0
  have hk0 : σ0.kheap t = some (.tcb { x with tcbState := .restart }) := by
    rw [hσ0, stsAct_kheap]; simp [updK]
  have hc0 : σ0.curThread = t := by
    rw [hσ0]; unfold stsAct; split_ifs <;> exact hct
  intro y hy
  obtain ⟨y', hy', -, hs⟩ := hK1.tcb hk0
  rw [hK1.ct, hc0, hy'] at hy; cases hy
  rcases hs with e | ⟨h, -⟩
  · rw [e]; rfl
  · exact h.elim

/-- `return_consumed` returns a word (the consumed time), so Consumed
always replies. -/
theorem returnConsumed_ne_nil {p : Fl4Spec.ObjRef} {σ σ' : Fl4Spec.State Unit} {d : List Fl4Spec.Data}
    (h : (d, σ') ∈ (Fl4Spec.returnConsumed (Z := Unit) p σ).1) : d ≠ [] := by
  unfold Fl4Spec.returnConsumed at h
  rw [nd_bind_apply'] at h
  obtain ⟨⟨c, σm⟩, -, h2⟩ := h
  rw [nd_pure_apply'] at h2
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h2)
  simp [Fl4Spec.wordsFromTime]

set_option maxHeartbeats 2000000 in
/-- **The SchedControl cap on `JAt`, `JAt` after** (module docstring). -/
theorem sched_controlJ_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (hres : σ.schedulerAction = .resumeCurThread)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hcpu : cpu = Z.c) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hsb : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (hsc : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ Z.C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ Z.T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    (hpi : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p.bv ≠ σ.idleSc)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ' inv σ1,
        (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv) (excaps.map Prod.fst)).run σ =
          ({(.ok inv, σ)}, False) →
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄) :
    syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ∧
        ((σ' = σ ∧ r.2.1 = s ∧ r.2.2 = a ∧ ∃ e', (specDec fp slbl (args.map UScalar.bv) ci sl (.SchedControl cpu)
            excaps buffer).run σ = ({(.error e', σ)}, False)) ∨
          (r.1 = .Ok () ∧ fp = false ∧ ∃ inv σ1,
            (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv)
              (excaps.map Prod.fst)).run σ = ({(.ok inv, σ)}, False) ∧
            Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
            Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False))) ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨hcur, xc, hkc, hrun⟩ := J.curRunnable hni hct
  have hC := J.curInv (by rw [hres]; simp)
  have key : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ res => (fp = true ∧ res = (.Err (.Sys (.InvalidCapability 0#u64)), s, a)) ∨
        (fp = false ∧ Sched.CPost σ (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv)
          (excaps.map Prod.fst)) s a
        (fun inv res => ∃ σ1 σ', Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
          Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) ∧
          res.1 = .Ok () ∧ SchedRel st Z.N Z.T Z.C Z.c res.2.1 σ' ∧ NtfnStateRel Z.N Z.T (L.mem res.2.1) σ' ∧
          NSC Z.N Z.C σ' ∧ Inv σ' ∧ P1.WritesIn st s res.2.1 (KFoot st Z.T Z.N Z.C Z.c s σ) ∧
          (σ1.schedulerAction = .resumeCurThread → IdleOK σ1 →
            (x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p.bv ≠ σ.idleSc) → ActIdle σ')) res) ⦄ := by
    unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_mono (decode_configure_refinesA htm Z.th s a σ hS hR J.nsc J.inv hC J.off lbl slbl hlbl cpu
        length buf ct hcpu hct args hlen hargs extra x0 hx0 _ hex hsb hsc hkc hrun) fun r h => Or.inr ⟨by trivial, h⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact Or.inl ⟨by trivial, by trivial⟩
  refine WP.spec_mono (WP.spec_and hArch (WP.spec_and key hRest)) ?_
  rintro ⟨r0, s', a'⟩ ⟨hA, hq, hRst⟩
  rcases hq with ⟨rfl, he⟩ | ⟨rfl, hq⟩
  · cases he; exact ⟨σ, Ac, Lst, D, J, Or.inl ⟨rfl, rfl, rfl, _, rfl⟩⟩
  rcases hq with ⟨e, e', he, hrun', -⟩ | ⟨inv, hdec, σ1, σ', he1, he2, hr1, hS', hR', hN', hI', hw, hAc⟩
  · cases he; exact ⟨σ, Ac, Lst, D, J, Or.inl ⟨rfl, rfl, rfl, e', run_liftME_err hrun'⟩⟩
  have hm1 : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by rw [he1]; exact Set.mem_singleton _
  have hm2 : ((), σ') ∈ (Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1).1 := by
    rw [he2]; exact Set.mem_singleton _
  have hK : ScTKw (fun p => p = ct.bv) σ σ' :=
    (tk_setThreadState hkc (ipcFree_of_runnable hrun) ipcFree_restart _ hm1).trans
      ((nkt_invokeSchedControlConfigureFlags inv σ1 ((), σ') hm2).mono fun _ h => h.elim)
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sc_step hX J.ip J.nk (WritesIn.tfoot_of_kfoot hw) hK hS' hR' fun h => hA _ h
  have hSOK : SOK (true, true) σ σ' :=
    (pres_setThreadState (f := (true, true)) _ _ σ _ hm1).trans
      (pres_invokeSchedControlConfigureFlags (true, true) _ σ1 _ hm2)
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hSOK⟩
  obtain ⟨Ac', hDbg, hKd, hBlk'⟩ := hRst hr1 σ' inv σ1 hdec he1 he2
  obtain ⟨a0, rest, hex', q, sz, rfl, b, per, k, badge, flag, rfl⟩ :=
    (rdp_decodeCfgHead slbl (args.map UScalar.bv) (excaps.map Prod.fst) σ _ (by rw [hdec]; exact Set.mem_singleton _)).2
      _ rfl
  have hB' : BlockedScActive σ' := bsa_configure J.bsa (hcur ▸ hkc) hrun (hcur ▸ hm1) hm2
  -- the configured SC is the extra cap's
  obtain ⟨p, sb, hx0n, hcap, hpq⟩ : ∃ p sb, x0 ≠ 0#u64 ∧ capAt (L.mem s) x0 = ok (.SchedContext p sb) ∧ p.bv = q := by
    rcases hex with ⟨-, he⟩ | ⟨hx0n, -, c, a1, rest', hc, hCR, -, he⟩
    · rw [he] at hex'; cases hex'
    rw [he] at hex'
    injection hex' with ha
    have hCa := hCR.abs
    rw [ha] at hCa
    cases c <;> simp only [absCap, reduceCtorEq, Fl4Spec.Cap.schedContextCap.injEq] at hCa
    exact ⟨_, _, hx0n, hc, hCa.1.symm⟩
  -- the mid-entry facts: the restart keeps them; Configure of another SC is `MidKn`
  have hcs : Fl4Spec.schedulable σ.curThread σ = true := ct_schedulable hC J.act J.inv (hcur ▸ hkc) hrun
  obtain ⟨hres1, hC1, hO1, hA1, hI1⟩ := restart_mid hcur hkc (hcur ▸ hcs) hres hC J.off J.act J.inv
  have hσ1 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he1
  rw [← hσ1] at hres1 hC1 hO1 hA1 hI1
  have hAI' : ActIdle σ' := hAc hres1 hA1.2 hpi
  have hctT : ct ∈ Z.T := J.thT ct (J.kern.curT ▸ by rw [show L.curW s = ct from P1.eq_of_bv (by rw [← J.kern.cur, hcur])])
  have hf1 := stsAct_fields (Fl4Proofs.P3.Notif.updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv
  have hct1 : σ1.curThread = ct.bv := by rw [hσ1, hf1.2.1]; exact hcur
  have hcs1 : σ1.curSc = σ.curSc := by rw [hσ1, hf1.2.2.1]; rfl
  have hid1 : σ1.idleThread = σ.idleThread := by
    rw [hσ1]; unfold Fl4Proofs.P3.Notif.stsAct; split_ifs <;> rfl
  obtain ⟨hC', hOw', hO'⟩ : MidA Z.T σ' := by
    obtain ⟨hpC, -, x, hkx, hbnd⟩ := hsc hx0n p sb hcap
    have hpc : p.bv ≠ ct.bv := fun e => by rw [e, hkc] at hkx; cases hkx
    have hkx1 : σ1.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) := by
      rw [hσ1, (stsAct_fields _ _).1]; simp [Fl4Proofs.P3.Notif.updK, hpc, hkx]
    obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
    by_cases hq : q = σ.curSc
    · -- the current SC, bound to the current thread: `commit_time`, a reschedule
      obtain ⟨y1, n1, hy1, hy1t⟩ := J.inv.back _ xt σ.curSc hkt hxs
      rw [← hq, ← hpq, hkx] at hy1; cases hy1
      have hci : σ1.curThread ≠ σ1.idleThread := by
        rw [hct1, hid1, ← hcur]; intro e
        obtain ⟨xi, hki, -, hti, -⟩ := J.act.2
        rw [← e, hkt] at hki; cases hki
        rw [hcur, hkc] at hkt; cases hkt; rw [hti] at hrun; cases hrun
      obtain ⟨kW, h0, hcn⟩ := mkw_configureCur (b := b) (per := per) (mr := k + Fl4Spec.MIN_REFILLS) (badge := badge)
        (flag := flag) (hpq ▸ hkx1) (by rw [hcs1]; exact hq) (by rw [hy1t, hct1, hcur]) hci
        (by simp [Fl4Spec.activeSc, Fl4Spec.MIN_REFILLS]) _ hm2
      exact kW.midA h0 hcn hC1 hI1 ⟨ct, hctT, hct1.symm⟩
    have ht : ∀ t, x.scTcb = some t → t ≠ σ1.idleThread ∧ t ≠ σ1.curThread := by
      intro t ht
      obtain ⟨-, xt', hkt', hxt'⟩ := hbnd ⟨t⟩ ht
      have hkt2 : σ.kheap t = some (.tcb xt') := hkt'
      refine ⟨fun e => ?_, fun e => ?_⟩
      · rw [hid1] at e
        obtain ⟨xi, hki, hsi, -⟩ := J.act.2
        rw [e, hki] at hkt2; cases hkt2; rw [hsi] at hxt'
        exact hpi hx0n p sb hcap (Option.some.inj hxt').symm
      · rw [hct1, ← hcur] at e
        rw [e, hkt] at hkt2; cases hkt2; rw [hxs] at hxt'
        exact hq (by rw [← hpq]; exact (Option.some.inj hxt').symm)
    have hK1 := mkn_configure (b := b) (per := per) (mr := k + Fl4Spec.MIN_REFILLS) (badge := badge) (flag := flag)
      (hpq ▸ hkx1) (by rw [hcs1]; exact hq) ht (by simp [Fl4Spec.activeSc, Fl4Spec.MIN_REFILLS])
      _ hm2
    exact hK1.mid3 hC1 hO1 hI1 ⟨ct, hctT, hct1.symm⟩
  have hF : FK σ σ' := ((fk_setThreadState _ _).of_eq he1).trans ((fk_invokeSchedControlConfigureFlags _).of_eq he2)
  have hwT := WritesIn.tfoot_of_kfoot hw
  -- the dead set: Configure cuts links only
  have hL : LK (fun _ => False) σ σ' := (lkm_setThreadState _ _ σ _ hm1).trans (lkm_configure _ σ1 _ hm2)
  have hP : ∀ p x, p = ct.bv → σ.kheap p = some (.tcb x) → Fl4Spec.runnable x.tcbState = true := by
    rintro p x rfl hk; rw [hkc] at hk; cases hk; exact hrun
  have hDead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hwT hK hP hL hF hAI'.1 hY' ((hSOK.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hCR'' : CurRun σ' := curRun_sc_step hkc hcur he1 (NKT.of_eq (nkt_invokeSchedControlConfigureFlags _) he2)
  exact ⟨σ', Ac', Lst', D, J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hwT hDead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2)) (J.sc_kern hwT hK hF hX' hDbg fun _ h => h)
    (J.sc_utc hwT hK hDbg) hN' hI' hC' (Or.inl (hC'.elim hOw' (curOwn_of_curInv hX'.fin.1.1.1 hI'))) hO' hAI' hB' (Or.inr (Or.inl hCR'')) hBlk'
    hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD,
    Or.inr ⟨hr1, rfl, _, σ1, hdec, he1, he2⟩⟩



set_option maxHeartbeats 4000000 in
/-- **The SchedContext cap on `JAt`** for Consumed, Bind, UnbindObject and a
YieldTo from an SC yielded to by none: when the invocation returns no data
(never for Consumed: `returnConsumed_ne_nil`), `JAt`
after (`XTop` by `xtop_sc_step`, the relations by `ScAll`, `BlockedScActive`
by `bk_invokeSchedContext` with Bind's decode check, `rdp_decodeBind`); a
YieldTo returning at once has replied (its `XTop` the reply leaf's, the
second disjunct, as Consumed always). Named per-op premise `hRest` (module
docstring). -/
theorem sched_contextJ_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction = .resumeCurThread)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ σ.idleSc)
    (hl : lbl = fl4_abi.label.SchedContextConsumed ∨ lbl = fl4_abi.label.SchedContextBind ∨
      lbl = fl4_abi.label.SchedContextUnbindObject)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ Z.N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (hslot : capAt (L.mem s) slot = ok (.SchedContext sc sb)) (hslotS : IsSlot Z.th slot) (hsb : sb.val < 64)
    (hssz : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → n + Fl4Spec.minSchedContextBits = sb.val)
    (hx0S : x0 ≠ 0#u64 → IsSlot Z.th x0)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ1, (∃ inv σ0,
        (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ = ({(.ok inv, σ)}, False) ∧
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
        Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({([], σ1)}, False)) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄) :
    syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => (∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ∧
          ((∃ e, r.1 = .Err e ∧ σ' = σ ∧ r.2.1 = s ∧ r.2.2 = a ∧ ∃ e',
              (specDec fp slbl args ci sl (.SchedContext sc sb) excaps buffer).run σ = ({(.error e', σ)}, False) ∧
              ErrRel e e') ∨
            (r.1 = .Ok () ∧ fp = false ∧ ∃ inv σ0,
              (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
                ({(.ok inv, σ)}, False) ∧
              Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
              Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({([], σ')}, False)))) ∨
        (r.1 = .Ok () ∧ L.mem r.2.1 (stA ct) ≠ sched.TS_RESTART ∧ fp = false ∧ ∃ inv σ0 data σ1,
          (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
            ({(.ok inv, σ)}, False) ∧
          Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
          Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({(data, σ1)}, False) ∧ data ≠ [] ∧
          ∃ σ2, ((), σ2) ∈ (Fl4Proofs.P3.specTail call ct.bv data σ1).1) ⦄ := by
  have hcapT : x0 ≠ 0#u64 → ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ Z.T := by
    intro hx p hc
    rcases hex with ⟨h0, -⟩ | ⟨-, -, c, a', rest, hc', -, hv, -⟩
    · exact absurd h0 hx
    · rw [hc] at hc'; cases eq_of_ok_eq hc'
      exact J.thT p hv
  have hcapN : x0 ≠ 0#u64 → ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ Z.N ∧ p ≠ 0#u64 := by
    intro hx p b w r hc
    rcases hex with ⟨h0, -⟩ | ⟨-, hS, -⟩
    · exact absurd h0 hx
    · obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hH : H p = some .ntfn := ((hJ.typed x0 hS).2.1 p b w r (capV_of_capAt hc)).2
      refine ⟨J.hset.2.1 p hH, fun e => ?_⟩
      rw [e, J.kern.h0] at hH; cases hH
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  obtain ⟨xc, -, -, -, hkc, -, hrunc, -⟩ := schedulable_inv hcs
  have hctT : ct ∈ Z.T := hct' ▸ hc.curT
  have key : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ res => (fp = true ∧ res = (.Err (.Sys (.InvalidCapability 0#u64)), s, a)) ∨
        (fp = false ∧ Sched.CPost σ (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)) s a
          (ScQ (fun s' σ' => ScAll (st := st) Z.N Z.T Z.C Z.R Z.c s σ s' σ' ∧
            ScFine (st := st) Z.N Z.T Z.C Z.c lbl sc ct s σ s' σ') σ ct call) res) ⦄ := by
    unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_mono (sc_decode_refines htm Z.th s a σ hS hR J.nsc J.inv J.yld J.act J.mcp J.c0 J.call J.rp
        J.rfree lbl slbl hlbl hsc hpi hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hmb hmax htu hmsg)
        fun r h => Or.inr ⟨by trivial, h⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact Or.inl ⟨by trivial, by trivial⟩
  refine WP.spec_mono (WP.spec_and hArch (WP.spec_and key hRest)) ?_
  rintro ⟨r0, s', a'⟩ ⟨hA2, hq, hRst⟩
  rcases hq with ⟨rfl, he⟩ | ⟨rfl, hq⟩
  · cases he; exact Or.inl ⟨σ, Ac, Lst, D, J, Or.inl ⟨_, rfl, rfl, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩⟩
  rcases hq with ⟨e, e', he, hrun, herr⟩ | ⟨inv, hrun, hr1, σ0, data, σ1, σ2, he0, he1, hcase, hall, hfine⟩
  · cases he; exact Or.inl ⟨σ, Ac, Lst, D, J, Or.inl ⟨e, rfl, rfl, rfl, rfl, e', run_liftME_err hrun, herr⟩⟩
  rcases hcase with ⟨hd, hσ⟩ | ⟨hdn, ⟨xr, hkr, hrs⟩, hdo⟩
  swap
  · -- FL4 has replied: the current thread `Running` (the TCB relation after)
    obtain ⟨y2, hky2, hrun2⟩ := running_after hkr hdo
    obtain ⟨x2, hkx2, hrel2⟩ := hall.1.2.1.tcb ct hctT
    rw [hky2] at hkx2; cases hkx2
    have hne : L.mem s' (stA ct) ≠ sched.TS_RESTART := by
      intro e
      have h1 := hrel2.st
      rw [hrun2] at h1
      rw [show tStA ct = stA ct by rw [tStA_eq, stA_eq], e, tsVals.2.1] at h1
      simp [tsCode] at h1
    exact Or.inr ⟨hr1, hne, rfl, inv, σ0, data, σ1, hrun, he0, he1, hdn, σ2,
      by rw [specTail_of_restart hkr hrs, hdo]; exact Set.mem_singleton _⟩
  left
  subst hd; subst hσ
  -- Consumed always replies: `return_consumed` returns a word
  replace hl : lbl = fl4_abi.label.SchedContextBind ∨ lbl = fl4_abi.label.SchedContextUnbindObject := by
    rcases hl with l | hl
    · exfalso
      have hg : Fl4Spec.genInvocationType slbl = .schedContextConsumed := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      have e : inv = .invokeSchedContextConsumed sc.bv :=
        (retP_pure (P := fun v => v = Fl4Spec.SchedContextInvocation.invokeSchedContextConsumed sc.bv) rfl :
          RetP _ (Fl4Spec.NonDetE.returnOk (Fl4Spec.SchedContextInvocation.invokeSchedContextConsumed sc.bv))).of_run hrun
      subst e
      have hm : (([] : List Fl4Spec.Data), σ2) ∈ (Fl4Spec.returnConsumed (Z := Unit) sc.bv σ0).1 := by
        rw [show Fl4Spec.returnConsumed (Z := Unit) sc.bv σ0 =
          Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextConsumed sc.bv) σ0 from rfl, he1]
        exact Set.mem_singleton _
      exact returnConsumed_ne_nil hm rfl
    · exact hl
  have hm0 : ((), σ0) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by rw [he0]; exact Set.mem_singleton _
  have hm1 : (([] : List Fl4Spec.Data), σ2) ∈ (Fl4Spec.invokeSchedContext (Z := Unit) inv σ0).1 := by
    rw [he1]; exact Set.mem_singleton _
  have hσ0 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he0
  have hko : ∀ q, q ≠ ct.bv → σ0.kheap q = σ.kheap q := fun q hq => by
    rw [hσ0, stsAct_kheap]; simp [updK, hq]
  have hkc0 : σ0.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ0, stsAct_kheap]; simp [updK]
  have hK0 : ScTKw (fun p => p = ct.bv) σ σ0 := tk_setThreadState hkc (ipcFree_of_runnable hrunc) ipcFree_restart _ hm0
  -- the invocation's shape, and Bind's decode check
  have hshape2 : ((∃ q cap, inv = .invokeSchedContextBind q cap) ∨
      (∃ q cap, inv = .invokeSchedContextUnbindObject q cap)) ∧
      ∀ q t, inv = .invokeSchedContextBind q (.threadCap t) → ScBindOK q t σ := by
    rcases hl with l | l
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨cap, rfl⟩ := (retP_bindDec _ _).of_run hrun
      refine ⟨Or.inl ⟨_, _, rfl⟩, fun q t e => ?_⟩
      have := ((rdp_decodeBind _ _ σ _ (by rw [hrun]; exact Set.mem_singleton _)).2 _ rfl) t
      cases e; exact this rfl
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
        rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run hrun
      exact ⟨Or.inr ⟨_, _, rfl⟩, fun q t e => by cases e⟩
  have hshape : ((∃ q cap, inv = .invokeSchedContextBind q cap) ∨ (∃ q cap, inv = .invokeSchedContextUnbindObject q cap) ∨
      (∃ q x n, inv = .invokeSchedContextYieldTo q ∧ σ0.kheap q = some (.schedContext x n) ∧ x.scYieldFrom = none)) ∧
      ∀ q t, inv = .invokeSchedContextBind q (.threadCap t) → ScBindOK q t σ :=
    ⟨hshape2.1.imp id Or.inl, hshape2.2⟩
  have hnY : ∀ p, inv ≠ .invokeSchedContextYieldTo p := by
    rcases hshape2.1 with ⟨q, cap, rfl⟩ | ⟨q, cap, rfl⟩ <;> intro p h <;> cases h
  obtain ⟨hshape, hbind⟩ := hshape
  have hK1 : ScTKw (fun _ => False) σ0 σ2 := tk_invokeSchedContext hshape _ hm1
  -- FL4's writes
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := by
    rcases hl with l | l
    · exact hfine.1 (Or.inl l)
    · exact hfine.1 (Or.inr l)
  have hX' : XTopAt (L := L) AR Z s' a' σ2 :=
    xtop_sc_step hX J.ip J.nk hW (hK0.trans (hK1.mono fun _ h => h.elim)) hall.1.1 hall.1.2.1 fun h => hA2 _ h
  obtain ⟨⟨-, -, hN', hI'⟩, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  -- `BlockedScActive`
  have hKb0 := bk_restart (hcur ▸ hkc) hrunc (hcur ▸ hm0)
  have hB0 := J.bsa.bk hKb0 (f1 := true) (pres_setThreadState (f := (true, true)) _ _ σ _ hm0)
  have hinv : (∃ q cap, inv = .invokeSchedContextBind q cap) ∨ (∃ q cap, inv = .invokeSchedContextUnbindObject q cap) ∨
      (∃ q, inv = .invokeSchedContextYieldTo q) := by
    rcases hshape with h | h | ⟨q, -, -, e, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨q, e⟩)
  have hB' : BlockedScActive σ2 := by
    have hu : decide (∀ p, inv ≠ .invokeSchedContextUnbind p) = true := by
      rcases hinv with ⟨q, cap, rfl⟩ | ⟨q, cap, rfl⟩ | ⟨q, rfl⟩ <;> simp
    exact hB0.bk (bk_invokeSchedContext hm1 hK1 hinv fun q t e => (hbind q t e).bk hKb0)
      (f1 := decide (∀ p, inv ≠ .invokeSchedContextYieldTo p))
      ((pres_invokeSchedContext inv σ0 _ hm1).weaken (f' := (decide (∀ p, inv ≠ .invokeSchedContextYieldTo p), true))
        id (fun _ => hu))
  obtain ⟨Ac', hDbg, hKd, hBlk'⟩ := hRst hr1 σ2 ⟨inv, σ0, hrun, he0, he1⟩
  -- the mid-entry facts: the restart keeps them, the invocation is a `MidK` step
  have hC := J.curInv (by rw [hres]; simp)
  obtain ⟨hres0, hC0, hO0, hA0, hI0⟩ := restart_mid hcur hkc hcs hres hC J.off J.act J.inv
  rw [← hσ0] at hres0 hC0 hO0 hA0 hI0
  have hf0 := stsAct_fields (Fl4Proofs.P3.Notif.updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv
  have hct0 : σ0.curThread = ct.bv := by rw [hσ0, hf0.2.1]; exact hcur
  have hcs0 : σ0.curSc = σ.curSc := by rw [hσ0, hf0.2.2.1]; rfl
  have hid0 : σ0.idleThread = σ.idleThread := by
    rw [hσ0]; unfold Fl4Proofs.P3.Notif.stsAct; split_ifs <;> rfl
  -- the current SC's thread is the current thread
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  obtain ⟨ycs, ncs, hkcs, hycs⟩ := J.inv.back _ xt σ.curSc hkt hxs
  -- the SC's bound thread (if any) is not idle (`hback`)
  have hnid : ∀ y n t, σ.kheap sc.bv = some (.schedContext y n) → y.scTcb = some t → t ≠ σ.idleThread := by
    intro y n t hy ht
    obtain ⟨x, n', hk, hx⟩ := hs.scs sc hsc
    rw [hk] at hy; cases hy
    rw [hx.tcb] at ht
    obtain ⟨h0, rfl⟩ := Sched.optRef_some ht
    exact (hback h0).2.2
  have hpc : sc.bv ≠ ct.bv := fun e => by
    obtain ⟨x, n', hk, -⟩ := hs.scs sc hsc; rw [e, hkc] at hk; cases hk
  have hMid : MidK σ0 σ2 := by
    rcases hl with l | l
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      have hpre := (rdp_decodeBindPre _ _ σ _ (by rw [hrun]; exact Set.mem_singleton _)).2 _ rfl
      obtain ⟨cap, rfl⟩ := (retP_bindDec _ _).of_run hrun
      cases cap
      case threadCap t =>
        obtain ⟨⟨y, n, hy, hyt⟩, xt0, hkt0, hxt0⟩ := hpre t rfl
        have hP : BindPre sc.bv t σ0 := by
          refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
          · rw [hcs0] at e; rw [e, hkcs] at hy; cases hy; rw [hycs] at hyt; cases hyt
          · rw [hct0, ← hcur] at e; rw [e, hkt] at hkt0; cases hkt0; rw [hxs] at hxt0; cases hxt0
          · rw [hid0] at e
            obtain ⟨xi, hki, hsi, -⟩ := J.act.2
            rw [e, hki] at hkt0; cases hkt0; rw [hsi] at hxt0; cases hxt0
        exact (mka_bind_ret (mka_schedContextBindTcb _ _) _) σ0 hP _ hm1
      case notificationCap n b r =>
        exact (mka_bind_ret (mka_schedContextBindNtfn _ _) _) σ0 trivial _ hm1
      all_goals exact (mka_fail (P := fun _ => True)) σ0 trivial _ hm1
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
        rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      have hpre := (rdp_decodeUnbindObjPre _ _ σ _ (by rw [hrun]; exact Set.mem_singleton _)).2 _ rfl
      obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run hrun
      cases cap
      case threadCap t =>
        obtain ⟨⟨y, n, hy, hyt⟩, htc⟩ := hpre t rfl
        have hP : sc.bv ≠ σ0.curSc ∧ ∀ y' n' t', σ0.kheap sc.bv = some (.schedContext y' n') → y'.scTcb = some t' →
            t' ≠ σ0.curThread ∧ t' ≠ σ0.idleThread := by
          refine ⟨fun e => ?_, fun y' n' t' hy' ht' => ?_⟩
          · rw [hcs0] at e; rw [e, hkcs] at hy; cases hy; rw [hycs] at hyt; cases hyt; exact htc rfl
          · rw [hko _ hpc, hy] at hy'; cases hy'; rw [hyt] at ht'; cases ht'
            rw [hct0, ← hcur, hid0]; exact ⟨htc, hnid y n t hy hyt⟩
        exact (mka_bind_ret (mka_schedContextUnbindTcb _) _) σ0 hP _ hm1
      case notificationCap n b r =>
        exact (mka_bind_ret (mka_schedContextUnbindNtfn _) _) σ0 trivial _ hm1
      all_goals exact (mka_fail (P := fun _ => True)) σ0 trivial _ hm1
  obtain ⟨hC', hOw', hO', hAI'⟩ := hMid.mid (T := Z.T) hres0 hC0 hO0 hA0 hI0 ⟨ct, hctT, hct0.symm⟩
  have hF : FK σ σ2 := ((fk_setThreadState _ _).of_eq he0).trans (fk_invokeSchedContext hshape _ hm1)
  have hCR'' : CurRun σ2 := curRun_sc_step hkc hcur he0 hK1
  have hKt := hK0.trans (hK1.mono fun _ h => h.elim)
  -- the dead set: the step cuts links only outside Bind's pair, which is covered (its caps)
  have hL : LK (invLinkW inv) σ σ2 := (lkm_setThreadState _ _ σ _ hm0).trans (lk_invokeSchedContext hshape _ hm1)
  have hP : ∀ p x, p = ct.bv → σ.kheap p = some (.tcb x) → Fl4Spec.runnable x.tcbState = true := by
    rintro p x rfl hk; rw [hkc] at hk; cases hk; exact hrunc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := J.kern.heap
  have scCov : (∀ k, Z.th sc = some k → Covered (L.mem s') Z.G sc.val (sc.val + max (objSize k) 1)) ∧
      (∀ k, H sc = some k → Covered (L.mem s') Z.G sc.val (sc.val + 2 ^ k.bits)) := by
    obtain ⟨x, n, hk, -⟩ := hs.scs sc hsc
    have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have hsz := hssz x n hk
    have hfit := hH.fits sc _ hHs
    simp only [P1.HKind.bits] at hfit
    rw [hsz] at hfit
    refine J.cover_cap hW hslotS hslot (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
      (range_sc sc sb hsb hfit) fun k hk' => ?_
    rw [hHs] at hk'; cases hk'
    exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  have hcovW : ∀ q ∈ D, invLinkW inv q.bv →
      (∀ k, Z.th q = some k → Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)) := by
    intro q _ hqW
    rcases hl with l | l
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨a0, rest, hex', rfl⟩ := (retP_bindHead _ _).of_run hrun
      rcases hex with ⟨-, he⟩ | ⟨hx0n, -, c, a1, rest', hc, hCR, hCV, he⟩
      · rw [he] at hex'; cases hex'
      rw [he] at hex'
      injection hex' with ha
      subst ha
      have hCa := hCR.abs
      have hxS := hx0S hx0n
      have hqsc : q.bv = sc.bv → q = sc := fun e => bv_inj e
      cases a1 with
      | threadCap t =>
        rcases hqW with e | e
        · rw [hqsc e]; exact scCov
        · cases c <;> simp only [absCap, reduceCtorEq, Fl4Spec.Cap.threadCap.injEq] at hCa
          rename_i p
          have hq : q = p := bv_inj (e.trans hCa)
          subst hq
          have hHp : H q = some .tcb := (hJ.tcb q).1 hCV
          have hfit := hH.fits q _ hHp
          simp only [P1.HKind.bits] at hfit
          refine J.cover_cap hW hxS hc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl (range_thread q hfit)
            fun k hk' => ?_
          rw [hHp] at hk'; cases hk'
          exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
      | notificationCap n b r =>
        rcases hqW with e | e
        · rw [hqsc e]; exact scCov
        · cases c <;> simp only [absCap, reduceCtorEq, Fl4Spec.Cap.notificationCap.injEq] at hCa
          rename_i p b' x1 x2
          have hq : q = p := bv_inj (e.trans hCa.1)
          subst hq
          have hty := hJ.typed x0 hxS
          rw [capV_of_capAt hc] at hty
          have hHp : H q = some .ntfn := (hty.2.1 q b' x1 x2 rfl).2
          have hfit := hH.fits q _ hHp
          simp only [P1.HKind.bits] at hfit
          refine J.cover_cap hW hxS hc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
            (range_ntfn q b' x1 x2 hfit) fun k hk' => ?_
          rw [hHp] at hk'; cases hk'
          exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
      | _ => exact hqW.elim
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
        rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run hrun
      exact hqW.elim
  -- the yield fields kept (no YieldTo here)
  have hYK2 : YKeep σ σ2 :=
    (((pres_setThreadState (f := (true, true)) _ _ σ _ hm0).weaken (f' := (true, false)) (fun _ => rfl)
        (fun h => absurd h (by decide))).trans
      ((pres_invokeSchedContext inv σ0 _ hm1).weaken (f' := (true, false)) (fun _ => decide_eq_true hnY)
        (fun h => absurd h (by decide)))).ykeep rfl
  have hDead : ∀ q ∈ {q | q ∈ D ∧ ¬ invLinkW inv q.bv}, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hW hKt hP hL hF hAI'.1 hY' (hYK2.dk q.bv) hq.2 (J.jcov.dead q hq.1)
  have hCov : ∀ q ∈ D, q ∉ {q | q ∈ D ∧ ¬ invLinkW inv q.bv} →
      (∀ k, Z.th q = some k → Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)) := fun q hq hn =>
    hcovW q hq (by_contra fun h => hn ⟨hq, h⟩)
  -- the TCB zombies' TCBs stay in the dead set: Bind's pair is named by the SC cap and the extra cap
  have hzW : ∀ p ∈ ZTcb (L := L) Z.th s, ¬ invLinkW inv p.bv := by
    intro p hp hqW
    have hqsc : p.bv = sc.bv → p = sc := fun e => bv_inj e
    rcases hl with l | l
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨a0, rest, hex', rfl⟩ := (retP_bindHead _ _).of_run hrun
      rcases hex with ⟨-, he⟩ | ⟨hx0n, -, c, a1, rest', hc, hCR, hCV, he⟩
      · rw [he] at hex'; cases hex'
      rw [he] at hex'
      injection hex' with ha
      subst ha
      have hCa := hCR.abs
      have hxS := hx0S hx0n
      have hscN : p = sc → False := fun e => J.not_ztcb hslotS
        (fun _ _ _ h => by rw [capV_of_capAt hslot] at h; cases h)
        (by rw [capV_of_capAt hslot, e]; simp [absCap, Fl4Spec.objRefs]) hp
      cases a1 with
      | threadCap t =>
        rcases hqW with e | e
        · exact hscN (hqsc e)
        · cases c <;> simp only [absCap, reduceCtorEq, Fl4Spec.Cap.threadCap.injEq] at hCa
          rename_i p'
          exact J.not_ztcb hxS (fun _ _ _ h => by rw [capV_of_capAt hc] at h; cases h)
            (by rw [capV_of_capAt hc]; show p.bv ∈ Fl4Spec.objRefs (absCap (.Thread p')); rw [e, hCa]
                simp [absCap, Fl4Spec.objRefs]) hp
      | notificationCap n b r =>
        rcases hqW with e | e
        · exact hscN (hqsc e)
        · cases c <;> simp only [absCap, reduceCtorEq, Fl4Spec.Cap.notificationCap.injEq] at hCa
          rename_i p' b' x1 x2
          exact J.not_ztcb hxS (fun _ _ _ h => by rw [capV_of_capAt hc] at h; cases h)
            (by rw [capV_of_capAt hc]; show p.bv ∈ Fl4Spec.objRefs (absCap (.Notification p' b' x1 x2))
                rw [e, hCa.1]; simp [absCap, Fl4Spec.objRefs]) hp
      | _ => exact hqW.elim
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
        rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run hrun
      exact hqW.elim
  exact ⟨σ2, Ac', Lst', _, J.sc_frame hW hKt hX' hCR' hRF' hY' hM' (J.sc_buf hW hKt) hRP' (J.sc_apart hW hKt)
    (J.sc_jpl hW hKt (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hW hDead hCov (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2)) (J.sc_kern hW hKt hF hX' hDbg fun _ h => h.1)
    (J.sc_utc hW hKt hDbg) hN' hI' hC' (Or.inl (hC'.elim hOw' (curOwn_of_curInv hX'.fin.1.1.1 hI'))) hO' hAI' hB' (Or.inr (Or.inl hCR'')) hBlk'
    hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 (fun p hp => ⟨J.zD p hp, hzW p hp⟩),
    Or.inr ⟨hr1, rfl, inv, σ0, hrun, he0, he1⟩⟩


/-- **The `set_consumed` reply at `J`** (ScXProd's `ScReplyLeaf` at `JAt`,
on the SchedContext decode's run) [W]: when FL4's decode has replied (the
caller `Running`: Consumed's `return_consumed`, or an at-once YieldTo's
`set_consumed` to the caller, then `set_thread_state Running`), the spec's
outcome after the restart, the invocation (`return_consumed`) and the reply
tail (`reply_from_kernel` when a call, `Running`) is at `JAt`. l4v:
`invoke_sched_context`'s `return_consumed`, its `sched_context_yield_to`
with the target not switched to, and `handle_invocation`'s reply, keep
`invs`. Consumed's case is proved (ScJointConsumed's `sc_consumedReplyJ`),
an at-once YieldTo's by ScJointYield's `decode_invocation_sched_context_yieldJ`. -/
def ScReplyJ (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (sc sb : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (ct : U64) : Prop :=
  syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
    ⦃ r => r.1 = .Ok () → L.mem r.2.1 (stA ct) ≠ sched.TS_RESTART → ∀ inv σ0 data σ1 σ2,
      (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
        ({(.ok inv, σ)}, False) →
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) →
      Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({(data, σ1)}, False) →
      ((), σ2) ∈ (Fl4Proofs.P3.specTail call ct.bv data σ1).1 →
      JAt (L := L) arI AR r.2.1 r.2.2 σ2 ⦄

/-- Bind's and UnbindObject's invocations return no data. -/
theorem invokeSc_data_nil {inv : Fl4Spec.SchedContextInvocation}
    (hinv : (∃ q cap, inv = .invokeSchedContextBind q cap) ∨ (∃ q cap, inv = .invokeSchedContextUnbindObject q cap))
    {σ0 σ1 : Fl4Spec.State Unit} {data : List Fl4Spec.Data}
    (h : Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({(data, σ1)}, False)) : data = [] := by
  have hm : (data, σ1) ∈ (Fl4Spec.invokeSchedContext (Z := Unit) inv σ0).1 := by rw [h]; exact Set.mem_singleton _
  rcases hinv with ⟨q, cap, rfl⟩ | ⟨q, cap, rfl⟩ <;> cases cap <;>
    simp only [Fl4Spec.invokeSchedContext] at hm <;>
    first
    | (rw [nd_bind_apply'] at hm
       obtain ⟨⟨u, σm⟩, -, h2⟩ := hm
       rw [nd_pure_apply'] at h2
       exact (Prod.mk.inj (Set.mem_singleton_iff.1 h2)).1)
    | (simp [Fl4Spec.NonDet.fail] at hm)

set_option maxHeartbeats 2000000 in
/-- **The SchedContext cap, `XCap` at `JAt`**, for Consumed, Bind and
UnbindObject: `sched_contextJ_step`'s outcome (the spec's decode failing
with the state unchanged, or the decode, restart and invocation with no
data and `JAtZ` after), else FL4 has replied: the invocation returned data
(`sched_contextJ_step`), so it is Consumed (Bind's and UnbindObject's return
none, `invokeSc_data_nil`), whose outcome is `ScReplyJ`'s (`hRep`,
ScJointConsumed's `sc_consumedReplyJ`). Premises as `sched_contextJ_step`'s. -/
theorem decode_invocation_sched_contextJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction = .resumeCurThread)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ σ.idleSc)
    (hl : lbl = fl4_abi.label.SchedContextConsumed ∨ lbl = fl4_abi.label.SchedContextBind ∨
      lbl = fl4_abi.label.SchedContextUnbindObject)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ Z.N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (hslot : capAt (L.mem s) slot = ok (.SchedContext sc sb)) (hslotS : IsSlot Z.th slot) (hsb : sb.val < 64)
    (hssz : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → n + Fl4Spec.minSchedContextBits = sb.val)
    (hx0S : x0 ≠ 0#u64 → IsSlot Z.th x0)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ1, (∃ inv σ0,
        (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ = ({(.ok inv, σ)}, False) ∧
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
        Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({([], σ1)}, False)) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄)
    (hRep : lbl = fl4_abi.label.SchedContextConsumed →
      ScReplyJ (L := L) (arI := arI) AR s a σ lbl length slot sc sb blk call don fp buf extra slbl excaps ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  have hJ := sched_contextJ_step s a σ J hres htm hmb hmax htu hmsg lbl slbl hlbl sb hsc hpi
    hl hback hbn hct hcs extra
    x0 hx0 excaps hex length slot buf blk call don fp args ci sl buffer hslot hslotS hsb hssz hx0S hArch hRest
  obtain ⟨r, hr, hp⟩ := spec_exists hJ
  have tr : ∀ P : core.result.Result Unit error.Exc × S × A → Prop, P r →
      syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra ⦃ P ⦄ :=
    fun P hP => by rw [hr]; exact (WP.spec_ok _).2 hP
  obtain ⟨hcur, -⟩ := J.curEq hct
  rcases hp with ⟨σ', Ac', Lst', D', J', ⟨e, h1, rfl, h2, h3, e', h4, h5⟩ | ⟨h1, rfl, inv, σ0, h2, h3, h4⟩⟩ |
    ⟨h1, hne, rfl, inv, σ0, data, σ1, h2, h3, h4, hdn, σ2, h5⟩
  · left
    refine tr _ (Or.inl ⟨e, h1, h2, ⟨e', h4, h5⟩, ?_⟩)
    exact ⟨_, _, _, _, _, _, J'⟩
  · left
    obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J'.xtop.rel
    refine tr _ (Or.inr ⟨.invokeSchedContext inv, DecOut.of_eq (run_liftME_ok h2), σ0, by rw [hcur]; exact h3, (.ok [], σ'),
      mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := ([], σ'))
        (by rw [h4]; exact Set.mem_singleton _),
      ⟨Z.th, Z.G, Or.inl ⟨h1, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ⟨_, _, _, _, _, _, J'⟩⟩)
  · right
    by_cases l44 : lbl = fl4_abi.label.SchedContextConsumed
    swap
    · exfalso
      refine hdn (invokeSc_data_nil ?_ h4)
      rcases hl.resolve_left l44 with l | l
      · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
        simp only [Fl4Spec.decodeSchedContextInvocation, hg] at h2
        obtain ⟨cap, rfl⟩ := (retP_bindDec _ _).of_run h2
        exact Or.inl ⟨_, _, rfl⟩
      · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
          rw [hlbl, l]; unfold scLabelOf; simp
        simp only [Fl4Spec.decodeSchedContextInvocation, hg] at h2
        obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run h2
        exact Or.inr ⟨_, _, rfl⟩
    have hR := hRep l44
    unfold ScReplyJ at hR
    rw [hr, WP.spec_ok] at hR
    have hX := hR h1 hne inv σ0 data σ1 σ2 h2 h3 h4 h5
    obtain ⟨Z2, H2, Cs2, Ac2, Lst2, D2, J2⟩ := hX
    obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J2.xtop.rel
    exact tr _ (Or.inr ⟨h1, hne, .invokeSchedContext inv, DecOut.of_eq (run_liftME_ok h2), σ0, by rw [hcur]; exact h3, data, σ1,
      mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := (data, σ1))
        (by rw [h4]; exact Set.mem_singleton _),
      ((), σ2), h5, ⟨Z2.th, Z2.G, hPl, hCR, hFI, hD, hMO⟩, ⟨Z2, H2, Cs2, Ac2, Lst2, D2, J2⟩⟩)

set_option maxHeartbeats 2000000 in
/-- **The SchedControl cap, `XCap` at `JAt`**: `decode_invocation_sched_controlJAt`'s
spec outcome with `sched_controlJ_step`'s `JAtZ` after (the spec's decode,
restart and Configure single-valued, so the step's state is the outcome's).
Premises as `sched_controlJ_step`'s. -/
theorem decode_invocation_sched_controlJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hcpu : cpu = Z.c) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hsb : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (hsc : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ Z.C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ Z.T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    (hpi : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p.bv ≠ σ.idleSc)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ' inv σ1,
        (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv) (excaps.map Prod.fst)).run σ =
          ({(.ok inv, σ)}, False) →
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄) :
    XCap (L := L) arI (JAt (L := L) arI AR) s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hXT := decode_invocation_sched_controlJAt s a σ J hni (by rw [hni.2]; simp) htm hmb hmax htu hmsg lbl slbl
    hlbl cpu length buf ct hcpu hct args hlen hargs extra x0 hx0 excaps hex hsb hsc slot blk call don fp ci sl buffer
    hArch
  have hJ := sched_controlJ_step s a σ J hni hni.2 htm hmb hmax htu hmsg lbl slbl hlbl cpu length buf ct hcpu hct args
    hlen hargs extra x0 hx0 excaps hex hsb hsc hpi slot blk call don fp ci sl buffer hArch hRest
  obtain ⟨hcur, -⟩ := J.curEq hct
  refine Or.inl (WP.spec_mono (WP.spec_and hXT hJ) ?_)
  rintro r ⟨hq, σ', Ac', Lst', D', J', hc⟩
  rcases hq with ⟨e, h1, h2, h3, -⟩ | ⟨inv', h1, σ1', h2, y, hy, h3, -⟩
  · refine Or.inl ⟨e, h1, h2, h3, ?_⟩
    rcases hc with ⟨rfl, -, -, -⟩ | ⟨hr1, -⟩
    · exact ⟨_, _, _, _, _, _, J'⟩
    · rw [h1] at hr1; cases hr1
  · refine Or.inr ⟨inv', h1, σ1', h2, y, hy, h3, ?_⟩
    rcases hc with ⟨-, -, -, e', he'⟩ | ⟨-, rfl, inv, σ1, hdec, he1, he2⟩
    · have hm := h1.1
      rw [he'] at hm
      exact absurd (Set.mem_singleton_iff.1 hm) (by simp)
    have hm : (specDec false slbl (args.map UScalar.bv) ci sl (.SchedControl cpu) excaps buffer).run σ =
        ({(.ok (Fl4Spec.Fl4Invocation.invokeSchedControl inv), σ)}, False) := run_liftME_ok hdec
    have hi := h1.1
    rw [hm] at hi
    have hi' := Set.mem_singleton_iff.1 hi
    simp only [Prod.mk.injEq, Except.ok.injEq, and_true] at hi'
    subst hi'
    rw [hcur, he1] at h2
    simp only [Prod.mk.injEq, Set.singleton_eq_singleton_iff, and_true, true_and] at h2
    subst h2
    obtain ⟨z, hz, hyz⟩ := mem_liftE_ret_inv (ε := Unit)
      (m := Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv) (b := ([] : List Fl4Spec.Data)) hy
    rw [he2] at hz
    rw [hyz, Set.mem_singleton_iff.1 hz]
    exact ⟨_, _, _, _, _, _, J'⟩

end

end

end Fl4Proofs.P3
