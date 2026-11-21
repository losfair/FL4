/-
P3 (DESIGN.md §9), KENTRY-PLAN g2h (d1): **the `Steps`-based cap leaves end
in `LiveDN`**: IRQ control, IO port control, IRQ handler, DomainSet and the IO
port cap (every label), with the posts `JAtL` (XTopJointWJPL) in place of
`JAt`, from `LiveDN` and `SpecGlob` at the decode's state (`ZNoBlk` by
`JAtZ.zNoBlk`). No `JStepHyps` / `JReplyHyp` premise is needed any more:
`Steps.jatL` (XTopJointLiveStep) needs none, and the reply step is proved
here.

* `JAtZ.runJD` (moved to XTopJointReply in g2i, `runJ` its corollary):
  `set_thread_state Running` of a `Restart` thread with the dead set `D`
  named in the post, and the slot (`tfoot_oobj`) and debug-word
  (`running_blk`'s `Foot`) frames.

* `JAtZ.regWrSD`: one register write of a thread keeps the slots
  (`tcb_oobj`: a TCB word at offset 256..447) and the debug words
  (`foot_field`).
* `JAtZ.reply1JL`: `reply1` (the reply registers when called, then
  `Running`) keeps `LiveDN`: XTopJointReply's `reply1J` started from
  `J.addDeadSet`, `LiveDN.of_jstep` at the end.
* `portInTail_jatL`, `decode_invocation_ioport_inJL`,
  `decode_invocation_ioportJ_stepsL`: XTopJointPortIn's chain at `JAtL`.
* `IrqSteps.jatL`, `decode_invocation_irq_handlerJLL`: XTopJointIrqL's at
  `JAtL`: the primitive steps by `Steps.jatL`; after the deletion of a
  notification cap `WJL` carries `LiveDN` and `SpecGlob`.
* `decode_invocation_irq_controlJ_stepL`,
  `decode_invocation_ioport_controlJ_stepL`, `decode_invocation_domainJ_stepL`:
  XTopJointStep's wrappers at `JAtL`.
-/
import Fl4Proofs.P3.XTopJointLiveCn
import Fl4Proofs.P3.XTopJointReply
import Fl4Proofs.P3.XTopJointIrqL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **One register write of a thread keeps the slots and the debug words**
(module docstring). -/
theorem JAtZ.regWrSD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (r : Fl4Spec.Register) (v : U64) :
    SlotsSame Z.th (L.mem s) (L.mem (L.wr s (regA t (regIdx r)) v)) ∧
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s (L.wr s (regA t (regIdx r)) v) := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hT
  have hil := regIdx_lt r
  set K : U64 := ⟨BitVec.ofNat 64 (256 + 8 * (regIdx r).val)⟩ with hKdef
  have hKv : K.val = 256 + 8 * (regIdx r).val := by
    show (BitVec.ofNat 64 (256 + 8 * (regIdx r).val)).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hra : (regA t (regIdx r)).val = t.val + 256 + 8 * (regIdx r).val := regA_val hta hil
  have hKt : (core.num.U64.wrapping_add t K).val = t.val + K.val := tfield_val hta (by rw [hKv]; omega)
  have hreq : regA t (regIdx r) = core.num.U64.wrapping_add t K :=
    UScalar.eq_of_val_eq (by rw [hra, hKt, hKv]; omega)
  have hwr : P1.WritesIn st s (L.wr s (regA t (regIdx r)) v) (· = regA t (regIdx r)) :=
    writesIn_wr (a_reg hta r).1
  refine ⟨J.xtop.slotsSame_of hwr fun b hb => ?_, P1.Foot.dbgKeep J.blk (Set.empty_subset _) ?_⟩
  · rw [hb, hreq]; exact tcb_oobj ht hta (by rw [hKv]; omega) (by rw [hKv]; omega)
  · rw [hreq]
    exact foot_field hTH htH (by rw [hKv]; omega) (by rw [hKv]; omega) (by rw [hKv]; omega)
      ⟨by rw [hKv]; omega, by rw [hKv]; omega⟩


set_option maxHeartbeats 16000000 in
/-- **`reply1` at `J` keeps `LiveDN`** (XTopJointReply's `JAtZ.reply1J` from
`J.addDeadSet`, with `runJD` and `regWrSD`; `LiveDN.of_jstep` at the end). -/
theorem JAtZ.reply1JL (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hL : LiveDN (L := L) Z.th H Cs Z.G s σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart) (call : Bool) (v : U64) :
    vspace.reply1 st s ct call v ⦃ s2 => ∀ z ∈ (specTail call ct.bv [v.bv] σ).1, JAtL (L := L) arI AR s2 a z.2 ⦄ := by
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.1.ztcb
  unfold vspace.reply1
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_mono (J0.runJD hct hk hrs) ?_
    rintro s2 ⟨Lst', J2, hSS, hK⟩ z hz
    rw [specTail_restart hk hrs false v.bv] at hz
    simp only [Bool.false_eq_true, ↓reduceIte] at hz
    rw [Notif.setThreadState_eq .running hk] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨_, _, _, _, _, _, J2, LiveDN.of_jstep J hL J2 rfl rfl hSS hK
      (orig_eq_of_slots J.xtop.rel.2.1.2.2.2.1 J2.xtop.rel.2.1.2.2.2.1 J.kern.orig J2.kern.orig hSS)
      (by unfold Notif.stsAct; split <;> rfl) fun p hp => Or.inr hp⟩
  · simp only [↓reduceIte]
    have hin : (do
        let buf ← msg.lookup_ipc_buffer st s true ct
        let s2 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
        let (n, s3) ← msg.set_mr st s2 ct buf 0#u64 v
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
        msg.set_msg_info st s3 ct mi) ⦃ s3 => ∃ w : U64,
          s3 = L.wr (L.wr (L.wr s (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
            (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w ∧
          w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 1, 0, 0, 0⟩ ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s true ct L.total) ?_
      rintro buf -
      refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
      rintro s1 rfl
      have hset : ∀ s1 : S, msg.set_mr st s1 ct buf 0#u64 v ⦃ r =>
          r = (1#u64, L.wr s1 (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) ⦄ := by
        intro s1
        unfold msg.set_mr
        have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
        simp only [h4, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
        rintro r0 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ v) ?_
        rintro s2 rfl
        simp only [lift, bind_ok, WP.spec_ok]
        rfl
      refine WP.spec_bind (hset _) ?_
      rintro r rfl
      unfold msginfo.MessageInfo.new
      simp only [bind_ok]
      refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 1#u64 (by decide)) ?_
      rintro s3 ⟨w, rfl, hw⟩
      refine ⟨w, ?_, by rw [hw]; exact msg_info_one_bv⟩
      rw [Endp.regIdx_badge, Endp.regIdx_msgInfo]
    refine WP.spec_bind hin ?_
    rintro s3 ⟨w, rfl, hw⟩
    -- the badge register
    have hXb := badge_wr_irel J0.ip (J0.xtop.irelK J0.ks J0.buf) hct hk 0#u64
    rw [badgeRegA_eq_regA] at hXb
    obtain ⟨V1, J1⟩ := J0.regWrJ hct hk Fl4Spec.badge_register 0#u64 hXb
    obtain ⟨hS1, hK1⟩ := J0.regWrSD hct Fl4Spec.badge_register 0#u64
    set x1 := setReg x Fl4Spec.badge_register (0#u64 : U64).bv with hx1
    have hk1 : (updK σ ct.bv (.tcb x1)).kheap ct.bv = some (.tcb x1) := by simp [updK]
    -- the message register
    have hX2 := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hct hk1 (Endp.mrIdx 0) (by decide) v
    obtain ⟨V2, J2⟩ := J1.regWrJ hct hk1 (Endp.mrIdx 0) v hX2
    obtain ⟨hS2, hK2⟩ := J1.regWrSD hct (Endp.mrIdx 0) v
    set x2 := setReg x1 (Endp.mrIdx 0) v.bv with hx2
    have hk2 : (updK (updK σ ct.bv (.tcb x1)) ct.bv (.tcb x2)).kheap ct.bv = some (.tcb x2) := by simp [updK]
    -- the message info
    have hX3 := reg_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hct hk2 Fl4Spec.msg_info_register (by decide) w
    obtain ⟨V3, J3⟩ := J2.regWrJ hct hk2 Fl4Spec.msg_info_register w hX3
    obtain ⟨hS3, hK3⟩ := J2.regWrSD hct Fl4Spec.msg_info_register w
    have hxC : setReg x2 Fl4Spec.msg_info_register w.bv = Endp.replyTcb x v.bv := by
      rw [hw]; rfl
    rw [updK_updK, updK_updK, hxC] at J3
    have hkC : (updK σ ct.bv (.tcb (Endp.replyTcb x v.bv))).kheap ct.bv = some (.tcb (Endp.replyTcb x v.bv)) := by
      simp [updK]
    -- `Running`
    refine WP.spec_mono (J3.runJD hct hkC hrs) ?_
    rintro s4 ⟨Lst', J4, hS4, hK4⟩ z hz
    rw [specTail_restart hk hrs true v.bv] at hz
    simp only [↓reduceIte] at hz
    rw [Notif.setThreadState_eq .running hkC] at hz
    rw [Set.mem_singleton_iff.1 hz]
    have hSS := ((hS1.trans hS2).trans hS3).trans hS4
    exact ⟨_, _, _, _, _, _, J4, LiveDN.of_jstep J hL J4 rfl rfl hSS
      (((hK1.trans hK2).trans hK3).trans hK4)
      (orig_eq_of_slots J.xtop.rel.2.1.2.2.2.1 J4.xtop.rel.2.1.2.2.2.1 J.kern.orig J4.kern.orig hSS)
      (by unfold Notif.stsAct; split <;> rfl) fun p hp => Or.inr hp⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}


set_option maxHeartbeats 8000000 in
/-- **The `In` tail at `JAtL`** (XTopJointPortIn's `portInTail_jat`: the
primitive steps by `Steps.jatL`, `reply1` by `JAtZ.reply1JL`). -/
theorem portInTail_jatL (hAM : ARMask arI AR) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hL : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hZ : ZNoBlk Z.th (L.mem s) (L.ksb s)) (hC : CurRun σ) {ct : U64} (hcur : σ.curThread = ct.bv)
    (port z : U64) (call : Bool)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a')) (hval : call = true → PortInVal arI) :
    portInTail (st := st) arI s ar ct port z call ⦃ res => res.1 = .Ok () ∧
      L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
          (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) (inData z.val)))).run σ1).1 ∧
        ∃ w ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) res.2.1 w.2 ∧
          JAtL (L := L) arI AR res.2.1 res.2.2 w.2 ⦄ := by
  have hX := J.xtop
  obtain ⟨htcb, x, hk⟩ := hX.curTcb hcur
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) :=
    Notif.setThreadState_eq .restart hk
  unfold portInTail
  have hts := WP.spec_and (set_thread_state_cpu (L := L) s ct sched.TS_RESTART)
    (spec_self (set_thread_state_cpu (L := L) s ct sched.TS_RESTART))
  refine WP.spec_bind hts ?_
  rintro s1 ⟨⟨hk1, hc1⟩, hr1⟩
  obtain ⟨v, a1, hv⟩ := hin ar port z
  rw [hv]; simp only [bind_ok]
  -- the spec's `In`
  obtain ⟨rr, ms, hu, hmem, hrr⟩ : ∃ rr, ∃ ms : Fl4Spec.MachineState,
      ms.underlyingMemory = σ1.machineState.underlyingMemory ∧
      (.ok rr, { σ1 with machineState := ms }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) (inData z.val)))).run σ1).1 ∧
      specTail call ct.bv rr { σ1 with machineState := ms } =
        specTail call ct.bv [v.bv] { σ1 with machineState := ms } := by
    cases call
    · obtain ⟨r, ms, hu, hmem⟩ := port_in_perform σ1 (BitVec.ofNat 16 port.val) z.val
      refine ⟨[r], ms, hu, hmem, ?_⟩
      have hky : ({ σ1 with machineState := ms } : Fl4Spec.State Unit).kheap ct.bv =
          some (.tcb { x with tcbState := .restart }) := by
        show σ1.kheap ct.bv = _; rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_self]
      rw [specTail_restart hky rfl false r, specTail_restart hky rfl false v.bv]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · obtain ⟨ms, hu, hmem⟩ := hval rfl ar a1 port z v hv σ1
      exact ⟨[v.bv], ms, hu, hmem, rfl⟩
  set σy : Fl4Spec.State Unit := { σ1 with machineState := ms } with hσy
  -- the restart and the access, as primitive steps
  have hstp : Steps (L := L) arI Z.th s ar σ s1 a1 σy :=
    ((Steps.restart arI hcur hk htcb hr1 (by rw [hcur]; exact hst) hC).trans arI
      (Steps.ksSpec arI (s := s1) (σ := σ1) (σ' := σy) (by constructor <;> first | rfl | exact hu) rfl rfl
        (fun h => ⟨h.st, h.node⟩) (fun h => h))).trans arI
      (Steps.arch arI (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨port, z, v, hv⟩))))))
  obtain ⟨G', V', Ac', Lst', D', J', hL', -⟩ := Steps.jatL hAM hstp rfl J hL hZ
  -- `reply1`
  set Z' : XSets := Z.mv G' V'
  have hXy := J'.xtop
  have hI : Vs.RInv (L := L) Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 Z'.N Z'.T Z'.C Z'.E Z'.R Z'.B Z'.c AR Z'.G s1 a1 σy :=
    ⟨hXy.rel.2.1, hXy.rel.2.2.1, hXy.rel.2.2.2.2.1, hXy.rel.2.2.2.1, hXy.fin⟩
  have hkY : σy.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    show σ1.kheap ct.bv = _; rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_self]
  have hcurY : ct.bv = σy.curThread := by
    show ct.bv = σ1.curThread; rw [hσ1, stsAct_cur]; exact hcur.symm
  have hR1 := Vs.reply1_invT s1 a1 σy hI ct htcb hcurY hkY rfl J'.kern.act call v
  refine spec_bind_assoc (WP.spec_and hR1 (spec_self hR1)) ?_
  rintro s3 ⟨⟨hne, hks3, w, hw, hI3, hz3⟩, heq⟩
  rw [WP.spec_ok]
  refine ⟨rfl, hne, fun σ1' hσ1' => ?_⟩
  have e : σ1' = σ1 := by
    rw [hst] at hσ1'
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hσ1'))).2).symm
  subst e
  have hSch := hI3.2.2.2.2.1.1.1
  have hXT : XTop (L := L) AR s3 a1 w.2 := ⟨Z', hI3.2.2.2.2, ⟨hXy.rel.1, hI3.1, hI3.2.1,
    hI3.2.2.2.1, hI3.2.2.1, by rw [hks3]; exact hXy.rel.2.2.2.2.2.1, hXy.rel.2.2.2.2.2.2.mono hz3⟩,
    IpcRel.of hI3.2.2.2.2.1.1.2.2.1 hI3.2.2.2.2.1.1.2.1 (sched_sc hSch), hXy.esa.mono hks3 hz3⟩
  refine ⟨rr, σy, hmem, w, by rw [hrr]; exact hw, hI3.relTop, ?_⟩
  have hRL := J'.reply1JL hL' (J.thT ct htcb) hkY rfl call v
  rw [show vspace.reply1 st s1 ct call v = ok s3 from heq, WP.spec_ok] at hRL
  exact hRL w hw

set_option maxHeartbeats 8000000 in
/-- **IOPort `In`** (labels 64..66, any `call`) at `JAtL` (XTopJointPortIn's
`decode_invocation_ioport_inJ` with `portInTail_jatL`). -/
theorem decode_invocation_ioport_inJL (hAM : ARMask arI AR) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hL : LiveDN (L := L) Z.th H Cs Z.G s σ) (hZ : ZNoBlk Z.th (L.mem s) (L.ksb s)) (lbl : U64)
    (hl : 64 ≤ lbl.val ∧ lbl.val ≤ 66)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel (inLabel (portSz lbl)))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536)
    (hC : CurRun σ)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a')) (call : Bool)
    (hval : call = true → PortInVal arI)
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKRMX (L := L) arI (JAtL (L := L) arI AR) s ar σ lbl length slot (.IoPort first last 0#u64) blk call don fp buf
      extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ0 : JAtL (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J, hL⟩
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hsz : portSz lbl = 1 ∨ portSz lbl = 2 ∨ portSz lbl = 4 := by unfold portSz; split_ifs <;> simp
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl (.IoPort first last 0#u64) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec
        (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
          (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val)))) := rfl
  rw [hspec, decode_in_eq slbl _ _ hsz hlbl]
  unfold ioport.decode
  simp only
  rw [hct, port_size_eq lbl ⟨hl.1, by omega⟩, is_port_in_eq lbl ⟨hl.1, by omega⟩]
  simp only [bind_ok]
  have hszU : (if lbl.val = 64 ∨ lbl.val = 67 then 1#u64 else if lbl.val = 65 ∨ lbl.val = 68 then 2#u64
      else 4#u64) = ⟨BitVec.ofNat 64 (portSz lbl)⟩ := by
    unfold portSz; split_ifs <;> rfl
  rw [hszU]
  have hsz0 : ¬ (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64) = 0#u64 := by
    rw [u64_eq_iff]; show ¬ (BitVec.ofNat 64 (portSz lbl)).toNat = 0
    rcases hsz with h | h | h <;> rw [h] <;> decide
  rw [if_neg hsz0, decide_eq_true (by omega : lbl.val ≤ 66)]
  simp only [↓reduceIte]
  -- the argument
  by_cases h1 : length < 1#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, run_liftME_err (run_liftME_err ?_), Or.inl trivial⟩, hJ0⟩
    unfold Fl4Spec.argsAtLeast
    rw [whenE_pos (show 1 > (args.map UScalar.bv).length by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  rw [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), lift, bind_ok]
  unfold Fl4Spec.argsAtLeast
  rw [whenE_neg (show ¬ 1 > ((y0 :: rest).map UScalar.bv).length by simp), retOk_bind, retOk_bind]
  have hmap : List.map UScalar.bv (y0 :: rest) = y0.bv :: rest.map UScalar.bv := rfl
  have g0 : (y0.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  rw [hmap, g0, the_some]
  set port := y0 &&& 65535#u64 with hport
  have hpv : port.val < 65536 := by rw [hport, and_ffff]; omega
  have hp16 : (Fl4Spec.ucast 16 y0.bv : BitVec 16) = BitVec.ofNat 16 port.val := by
    apply BitVec.eq_of_toNat_eq; rw [ucast16_toNat, BitVec.toNat_ofNat, hport, and_ffff]; omega
  rw [hp16]
  have hszv : (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64).val = portSz lbl := by
    show (BitVec.ofNat 64 (portSz lbl)).toNat = _
    rw [BitVec.toNat_ofNat]; rcases hsz with h | h | h <;> rw [h]
  rw [allowed_eq first last port _ hl16 hpv (by rw [hszv]; exact hsz)]
  simp only [hszv, bind_ok]
  have hens := ensure_run first last hfl hl16 port hpv hsz σ
  by_cases hc : port.val < first.val ∨ port.val + portSz lbl - 1 > last.val
  · rw [if_pos hc]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok]
    rw [if_pos hc] at hens
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err (run_liftME_err (run_bind_error hens _)),
      Or.inl trivial⟩, hJ0⟩
  rw [if_neg hc]
  rw [if_neg hc] at hens
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_mono (portInTail_jatL arI hAM J hL hZ hC hcur port ⟨BitVec.ofNat 64 (portSz lbl)⟩
    call hin hval) ?_
  rintro res ⟨hres, hne, hall⟩
  obtain ⟨htcb, x, hk⟩ := J.xtop.curTcb hcur
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)}, False) :=
    Notif.setThreadState_eq .restart hk
  obtain ⟨rr, σy, hy, z, hz, hRT, hXT⟩ := hall _ hst
  rw [hszv] at hy
  refine Or.inr ⟨hres, hne, .invokeArchObject (.spec (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val)
    (inData (portSz lbl))))), ?_, _, by rw [hcur]; exact hst, rr, σy, hy, z, hz, hRT, hXT⟩
  exact DecOut.of_eq (run_liftME_ok (run_liftME_ok ((run_bind_ok hens _).trans rfl)))

set_option maxHeartbeats 4000000 in
/-- **An IO port cap, `JAtL` after, every label** (XTopJointPortIn's
`decode_invocation_ioportJ_steps`; no `JStepHyps` / `JReplyHyp`). -/
theorem decode_invocation_ioportJ_stepsL [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (first last : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .IoPort first last 0#u64) (call : Bool)
    (hval : call = true → PortInVal arI)
    (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAtL (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IoPort first last 0#u64) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  have hZB := J.zNoBlk hsg
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨⟨-, hl, hfl⟩, -⟩ := slot_cap_wf hX hAs hsc
  have hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a') := by
    intro a p z
    obtain ⟨⟨v, a'⟩, h, -⟩ := spec_exists (hT.port_in a p z)
    exact ⟨v, a', h⟩
  have hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a' := by
    intro a p z d
    obtain ⟨a', h, -⟩ := spec_exists (hT.port_out a p z d)
    exact ⟨a', h⟩
  exact decode_invocation_ioportXS arI Z.th hX.rel.1 s ar σ lbl slbl hlbl length buf ct hct args hlen hargs hcur
    (hX.curTcb hcur).1 J.kern.act first last hfl (by simpa using hl) call hout rfl hX (J.curRun.run hni)
    (X := JAtL (L := L) arI AR) ⟨Z, H, Cs, Ac, Lst, D, J, hLv⟩
    (fun _ _ _ h => let ⟨_, V', Ac', Lst', D', J', hL', _⟩ := Steps.jatL hARI.toMask h rfl J hLv hZB
      ⟨_, H, Cs, Ac', Lst', D', J', hL'⟩)
    (fun _ _ _ h => JAt.xtop arI (JAtL.toJAt arI h))
    (cslotAddr sl) blk don fp extra ci sl excaps buffer
    (fun hI => Or.inr (decode_invocation_ioport_inJL arI hARI.toMask s ar σ J hLv hZB lbl hI slbl (hlbl.1 hI) length
      buf ct hct args hlen hargs hcur first last hfl (by simpa using hl) (J.curRun.run hni) hin call hval
      (cslotAddr sl) blk don fp extra ci sl excaps buffer))

set_option maxHeartbeats 4000000 in
/-- **`JAtL` after an IRQ handler invocation's run** (XTopJointIrqL's
`IrqSteps.jat`; module docstring). -/
theorem IrqSteps.jatL [Fl4Proofs.P1.PlainStore st] (hAM : ARMask arI AR) {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (h : IrqSteps (L := L) arI Z.th s ar σ s' a' σ') : JAtL (L := L) arI AR s' a' σ' := by
  rcases h with h | ⟨ct, s2, σ1, sl, p, b, w, r, s3, a3, σ3, hct, hs2, hst, -, hA, -, hk, hd, hm, h2⟩
  · obtain ⟨_, V', Ac', Lst', D', J', hL', -⟩ := Steps.jatL hAM h rfl J hLv (J.zNoBlk hsg)
    exact ⟨_, H, Cs, Ac', Lst', D', J', hL'⟩
  have hW := WJL.restart arI J hni hsg hP0 hLv hct s2 σ1 hs2 hst
  have hDS2 : DState (L := L) Z.th s2 σ1 Z.G := by
    obtain ⟨⟨V, Ac2, Lst2, D2, J2, -⟩, -⟩ := hW
    exact ⟨J2.xtop.rel.2.1, J2.del, J2.xtop.rel.2.2.1⟩
  have hd' := delete_oneJL arI Z H Cs (L.ksb s) rfl s2 ar σ1 Z.G hDS2 hW hA hk
  rw [hd, WP.spec_ok] at hd'
  obtain ⟨σ4, G4, hm4, -, -, -, -, hW4⟩ := hd'
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS2.1.1.abs_cap hA
  rw [hca.abs] at hg
  rw [capV_of_capAt hc] at hk; subst hk
  have e := (Det.detAt_capDeleteOne_ntfn hg).eq hm4 hm
  have e2 : σ4 = σ3 := congrArg Prod.snd e
  subst e2
  obtain ⟨⟨V4, Ac4, Lst4, D4, J4, -, -, hsg4, -⟩, hL4⟩ := hW4
  obtain ⟨_, V', Ac', Lst', D', J', hL', -⟩ :=
    Steps.jatL hAM h2 (Z := Z.mv G4 V4) rfl J4 hL4 (J4.zNoBlk hsg4)
  exact ⟨_, H, Cs, Ac', Lst', D', J', hL'⟩

set_option maxHeartbeats 4000000 in
/-- **An IRQ handler cap, `JAtL` after** (XTopJointIrqL's
`decode_invocation_irq_handlerJL`; module docstring). -/
theorem decode_invocation_irq_handlerJLL [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (irq : U64) (hsc : capV (L.mem s) (cslotAddr sl) = .IrqHandler irq)
    (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel Z.th (L.mem s) x0 excaps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hD : DomPlaced (L := L) Z.th s) (hP1 : IrqDelP1 (L := L) s ct irq)
    (length buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAtL (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IrqHandler irq) blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hirq : irq.val < 128 := (slot_cap_wf hX hAs hsc).1
  exact decode_invocation_irq_handlerXSD arI Z.th hX.rel.1 s ar σ Z.G J.dstate J.intL
    hX.fin.1.1.2.2.2.1 lbl slbl hlbl ct hct hcur (hX.curTcb hcur).1 J.kern.act (maskIrq_total arI hT) irq hirq hok
    (irqDelOKJL arI J hni hsg hP0 hLv hct irq hirq) (irqDelDKJ arI (jStepHyps arI) J hni hsg hct irq hirq)
    extra x0 hx0 excaps hex hxn hX.rel.2.2.2.2.1 hD hP1 rfl hX (J.curRun.run hni) _ ⟨Z, H, Cs, Ac, Lst, D, J, hLv⟩
    (fun _ _ _ h => IrqSteps.jatL arI hARI.toMask J hni hsg hP0 hLv h)
    (fun _ _ _ h => JAt.xtop arI (JAtL.toJAt arI h))
    length (cslotAddr sl) buf blk call don fp args ci sl buffer

set_option maxHeartbeats 4000000 in
/-- **The IRQ control cap, `JAtL` after** (XTopJointStep's
`decode_invocation_irq_controlJ_step`; no `JStepHyps`). -/
theorem decode_invocation_irq_controlJ_stepL (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hAR : ArchIrqRel arI ar σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAtL (L := L) arI AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  have hX := J.xtop
  have hZB := J.zNoBlk hsg
  obtain ⟨hcur, -⟩ := J.curEq hct
  exact decode_invocation_irq_controlXS arI Z.th s ar σ Z.G J.intL hHA lbl slbl hlbl hrm length
    buf ct hct args hlen hargs hcur J.kern.act hact2 extra x0 hx0 excaps hex hps hls hsrcC nA hnum hnA
    (maskIrq_total arI hT) hAR rfl rfl hX (J.curRun.run hni) _ ⟨Z, H, Cs, Ac, Lst, D, J, hLv⟩
    (fun _ _ _ h => let ⟨_, V', Ac', Lst', D', J', hL', _⟩ := Steps.jatL hARI.toMask h rfl J hLv hZB
      ⟨_, H, Cs, Ac', Lst', D', J', hL'⟩)
    (fun _ _ _ h => JAt.xtop arI (JAtL.toJAt arI h))
    blk call don fp ci buffer

set_option maxHeartbeats 4000000 in
/-- **The IO port control cap, `JAtL` after** (XTopJointStep's
`decode_invocation_ioport_controlJ_step`; no `JStepHyps`). -/
theorem decode_invocation_ioport_controlJ_stepL (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAtL (L := L) arI AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  have hX := J.xtop
  have hZB := J.zNoBlk hsg
  obtain ⟨hcur, -⟩ := J.curEq hct
  exact decode_invocation_ioport_controlXS arI Z.th s ar σ Z.G J.ioLay hPA lbl slbl hlbl length
    buf ct hct args hlen hargs hcur J.kern.act hact3 extra x0 hx0 excaps hex hps hls hsrcC rfl rfl hX (J.curRun.run hni) _
    ⟨Z, H, Cs, Ac, Lst, D, J, hLv⟩
    (fun _ _ _ h => let ⟨_, V', Ac', Lst', D', J', hL', _⟩ := Steps.jatL hARI.toMask h rfl J hLv hZB
      ⟨_, H, Cs, Ac', Lst', D', J', hL'⟩)
    (fun _ _ _ h => JAt.xtop arI (JAtL.toJAt arI h)) blk call don fp ci buffer

set_option maxHeartbeats 4000000 in
/-- **The domain cap, `JAtL` after** (XTopJointStep's
`decode_invocation_domainJ_step`; no `JStepHyps`). -/
theorem decode_invocation_domainJ_stepL (hcfg : DomConfig) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects Z.th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel Z.th (L.mem s) x0 excs)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAtL (L := L) arI AR) s ar σ lbl length slot .Domain blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excs buffer ct := by
  have hX := J.xtop
  have hZB := J.zNoBlk hsg
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hP := hX.fin.1.2
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hC := J.curRun.run hni
  have hA : Notif.ActReady σ := J.inv.actReady
  exact decode_invocation_domainXS arI hcfg Z.th hX.rel.1 s ar σ Z.G hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 ct hct
    hcur (hX.curTcb hcur).1 J.kern.act hkf hP.vs.ksb_al hksO hactK lbl slbl hlbl length buf args hlen hargs extra x0
    hx0 excs hex (domSetHyp_of hX J.thT hC hA hcur) (domResHyp_of hX J.ks J.thT hC hA hcur)
    (domStallHyp_of arI hX.fin.1.1.1 J.thT) hC ⟨Z, H, Cs, Ac, Lst, D, J, hLv⟩
    (fun _ _ _ h => let ⟨_, V', Ac', Lst', D', J', hL', _⟩ := Steps.jatL hARI.toMask h rfl J hLv hZB
      ⟨_, H, Cs, Ac', Lst', D', J', hL'⟩)
    (fun _ _ _ h => JAt.xtop arI (JAtL.toJAt arI h))
    slot blk call don fp ci sl buffer

end

end

end Fl4Proofs.P3
