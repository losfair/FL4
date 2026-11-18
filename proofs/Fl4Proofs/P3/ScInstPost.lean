/-
P3 (DESIGN.md §9), scheduling contexts: **`SchedTailHyp` discharged**
(the post-install premises of SetSchedParams' scheduler step).

* FL4: the caller's restart (P1's `restart_ok`, `restart_blk`), then the
  fault-handler install by P1's `install_tcb_cap.cai` (`hcap`: the old
  fault-handler cap is null or an endpoint, `FhSlotHyp`; `hslot`:
  `inst_hslot`), with `set_priority`'s and `bind_tcb`'s/`unbind_tcb`'s
  conditions carried by `CaiFr` (`conds_caifr`), then `schedTail_foot`.
* The spec: `SpecPost` after the restart (`specPost_restart`, from `Inv`
  and the decoder's checks `ScDec`), then across the install: `install_sk`
  when the old cap is null or a non-final endpoint cap, `finEpSpecHyp`
  (proved from ScCancelFrame's `capDelete_ep_post`: what `cancel_all_ipc`
  keeps) when it is a final one; then `set_mcpriority`, `set_priority` and
  the SC step as in `schedTailHyp_of`/`scSpecHyp_of`/`bindSpecHyp_of`.
* `hRT_of`, `hRS_of`: the FL4/spec agreement on the target and the SCs from
  `SchedRel`, `NtfnStateRel` and P1's `SCsOK`, with the placement
  hypothesis `ScSetsHyp` (the spec's SCs are among `C` and P1's `Scs`).
-/
import Fl4Proofs.P3.ScCancelFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

section Spec
open Fl4Spec

/-- **The spec's fault-handler install over a final endpoint cap keeps
`SpecPost`** (proved: `finEpSpecHyp`) (its `cap_delete` runs `cancel_all_ipc`: the
endpoint's waiters restarted and enqueued if schedulable, a reschedule;
the target's SC links, the SCs and the other endpoints and notifications
are kept, and a target with no SC is not enqueued). -/
def FinEpSpecHyp : Prop :=
  ∀ (σ1 σ2 : State Unit) (p : ObjRef) (x : Tcb) (ssl : CslotPtr) (fh : Cap × CslotPtr)
    (sco : Option (Option ObjRef)),
    σ1.kheap p = some (.tcb x) → (∃ e b R, x.tcbFaultHandler = .endpointCap e b R) →
    isFinalCap' x.tcbFaultHandler σ1 →
    (.ok (), σ2) ∈ ((installTcbCap (Z := Unit) p ssl 3 (some fh)).run σ1).1 →
    SpecPost σ1 p sco → SpecPost σ2 p sco

/-- **`FinEpSpecHyp` holds** (the old cap need not be final: `capDelete_ep_post`
for the delete, `SK` for the checks and the insert). -/
theorem finEpSpecHyp : FinEpSpecHyp := by
  intro σ1 σ2 p x ssl fh sco hk ⟨e, b, R, hfe⟩ _ hx hpost
  obtain ⟨nc, sl⟩ := fh
  unfold installTcbCap at hx
  dsimp only at hx
  obtain ⟨z, hz, ⟨a, ha, hx⟩ | ⟨e', he, hx⟩⟩ := bindE_mem_inv hx
  · have hg : getCap (Z := Unit) (p, tcbCnodeIndex 3) σ1 = ({(.endpointCap e b R, σ1)}, False) := by
      rw [getCap_tcb_three hk, hfe]
    have hz' : (.ok (), z.2) ∈ ((capDelete (Z := Unit) (p, tcbCnodeIndex 3)).run σ1).1 := by
      have : z = (.ok (), z.2) := by obtain ⟨r, s⟩ := z; simp only at ha; subst ha; rfl
      rw [← this]; exact hz
    have hP := capDelete_ep_post hg hz' p sco hpost
    unfold NonDetE.unlessE at hx
    split at hx
    · have hx' : ((.ok (), σ2) : Except Unit Unit × State Unit) ∈ ({(.ok (), z.2)} : Set _) := hx
      rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hx')).2]; exact hP
    · obtain ⟨w, hw, ew⟩ := liftE_mem_inv hx
      simp only at ew
      rw [ew]
      exact hP.sk (psk_checkCapAt _ _ (psk_checkCapAt _ _ (psk_capInsert _ _ _)) z.2 w hw)
  · cases hx

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

theorem tcb_slot_fault (t : U64) :
    obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER = ok (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) := by
  rw [spec_eq_ok (tcb_slot_spec t _), tcb_root_eq t _ (n := 3) (by decide)
    (by simp [layout.tcb.SLOT_FAULT_HANDLER])]

/-- **Hypothesis: every TCB's fault-handler slot holds the null cap or an
endpoint cap of P1's heap** (l4v `valid_tcb`'s `valid_fault_handler`). -/
def FhSlotHyp (th : TypedHeap) (H : Heap) (s : S) : Prop :=
  ∀ t, th t = some .tcb → NullOrEp H (capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)))

/-- `set_priority`'s and `bind_tcb`'s/`unbind_tcb`'s conditions across a
`CaiFr` step (`tcs_conds_of_caifr` without the flags). -/
theorem conds_caifr {s0 s1 : S} {p sc : U64} {scf : Bool} (hT : TcbPlaced T) (ht : p ∈ T)
    (F : CaiFr st T Scs 0#u64 s0 s1) (ha : L.actionW s1 = L.actionW s0 ∨ L.actionW s1 = 1#u64)
    (hc : p = L.curW s0 → (L.mem s0 (inqA p) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s0 (scA p) ≠ 0#u64 ∧
      L.mem s0 (scA p) ∈ Ac)
    (hbind : scf = true → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s0 (scA p) = 0#u64 ∧
      L.mem s0 (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s0 (P1.stA p)) → sc ∈ Ac))
    (hunb : scf = true → sc = 0#u64 → L.actionW s0 ≠ p ∧ L.idleW s0 ≠ p) :
    (p = L.curW s1 → (L.mem s1 (inqA p) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s1 (scA p) ≠ 0#u64 ∧
        L.mem s1 (scA p) ∈ Ac) ∧
    (scf = true → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s1 (scA p) = 0#u64 ∧
      L.mem s1 (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s1 (P1.stA p)) → sc ∈ Ac)) ∧
    (scf = true → sc = 0#u64 → L.actionW s1 ≠ p ∧ L.idleW s1 ≠ p) := by
  refine ⟨fun e => ?_, fun hf h0 => ?_, fun hf h0 => ?_⟩
  · rw [F.cur] at e
    obtain ⟨r0, b0, a0⟩ := hc e
    refine ⟨?_, by rw [F.sc p ht]; exact b0, by rw [F.sc p ht]; exact a0⟩
    by_contra hn
    exact F.rel p ht hn r0
  · obtain ⟨hsc, h1, h2, h3⟩ := hbind hf h0
    refine ⟨hsc, by rw [F.sc p ht]; exact h1, by rw [F.stc sc hsc]; exact h2, fun hb => ?_⟩
    rcases F.st p ht with e | e | e
    · rw [e] at hb; exact h3 hb
    · rw [e] at hb
      rcases hb with hb | hb
      · exact absurd hb not_blocked_restart
      · exact absurd hb restart_ne.1
    · rw [e] at hb
      rcases hb with hb | hb
      · exact absurd hb not_blocked_inactive
      · exact absurd hb inactive_ne.1
  · obtain ⟨h1, h2⟩ := hunb hf h0
    refine ⟨?_, by rw [F.idle]; exact h2⟩
    rcases ha with e | e
    · rw [e]; exact h1
    · rw [e]; intro e'; exact notT_small hT (by rw [← e']; decide) ht

/-- **FL4's fault-handler install keeps `BlkOK` with the `CaiFr` frame**
(P1's `install_tcb_cap.cai`, its `hcap` from `FhSlotHyp`, its `hslot` by
`inst_hslot`). -/
theorem inst_fl4 (th : TypedHeap) (hP : Placed th) (hSC : SlotCapW th T Ω Sg) {s1 : S} {G : MdbGhost}
    (hM : MdbLinks th (L.mem s1) G) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (p : U64)
    (hp : th p = some .tcb) (hcap : NullOrEp H (capV (L.mem s1) (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3))))
    (slot src : U64) (hs : IsSlot th src) (nc : capability.Cap) (a : A) (s2 : S) (a1 : A)
    (hins : tcb.install_tcb_cap st arI s1 a p slot layout.tcb.SLOT_FAULT_HANDLER nc src = ok (.Ok (), s2, a1)) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ CaiFr st T Scs 0#u64 s1 s2 ∧
      (L.actionW s2 = L.actionW s1 ∨ L.actionW s2 = 1#u64) := by
  have hr : IsSlot th (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3)) :=
    AbsSlot.isSlot ⟨p, rfl, Or.inr ⟨hp, 3, by decide, rfl⟩⟩
  have := tcb.install_tcb_cap.cai (ar := arI) s1 a p slot _ nc src _ (tcb_slot_fault p) h
    (by rw [slot_cap_eq, capAt_capV]; exact (WP.spec_ok _).2 hcap)
    (inst_hslot (ar := arI) hP hSC hM hr hs p slot nc)
  rw [hins, WP.spec_ok] at this
  exact this

/-- **`SchedTailHyp` discharged**: FL4 by the caller's restart (P1's
`restart_ok`, `restart_blk`, `restart_hB`), the install (`inst_fl4`, the
conditions carried by `conds_caifr`) and `schedTail_foot`; the spec by
`specPost_restart`, `install_sk` or `FinEpSpecHyp`, then `set_mcpriority`,
`set_priority` and the SC step. The hypotheses: P1's invariants at entry
(`BlkOK`, the caller running with a released active SC, the scheduler
action `RESUME`, `KWOut`), the placement `SlotCapW`, the fault-handler
slots `FhSlotHyp`; the FL4/spec agreement on the target's SC and blocking
and the SCs' membership, `TCB` and activity (`hRT`, `hRS`, from the
scheduler relations: `hRT_of`, `hRS_of`); the spec's `Inv`, the caller
runnable, `BlkQ` and `BlkIn`. -/
theorem schedTailHyp_disch (hA : P0.ArchTotal arI) (th : TypedHeap) (hP : Placed th)
    (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hnb : ¬ Blocked (L.mem s (P1.stA (L.curW s)))) (hnr : L.mem s (P1.stA (L.curW s)) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hcurC : (L.mem s (inqA (L.curW s)) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA (L.curW s)) ≠ 0#u64 ∧
      L.mem s (scA (L.curW s)) ∈ Ac)
    (hTh : ∀ t, th t = some .tcb → t ∈ T) (hK : KWOut (st := st) th T Cs Sg Scs Z (EH H) s)
    (hSC : SlotCapW th T Ω Sg) (hFh : FhSlotHyp (L := L) th H s) (hact0 : L.actionW s = 0#u64)
    (hRT : ∀ q x, th q = some .tcb → σ.kheap q.bv = some (.tcb x) →
      (x.tcbSchedContext = none → L.mem s (scA q) = 0#u64) ∧
      (BlockedR (L.mem s (P1.stA q)) → Fl4Spec.ipcQueuedThreadState x.tcbState = true))
    (hRS : ∀ (c : U64) y n, c ≠ 0#u64 → σ.kheap c.bv = some (.schedContext y n) →
      c ∈ Scs ∧ (y.scTcb = none → L.mem s (scTcbA c) = 0#u64) ∧ (Fl4Spec.scReleased σ.curTime y = true → c ∈ Ac))
    (hInv : Inv σ) (hrun : ∀ xc, σ.kheap ct.bv = some (.tcb xc) → Fl4Spec.runnable xc.tcbState = true)
    (hQ : ∀ q x, th q = some .tcb → σ.kheap q.bv = some (.tcb x) →
      BlkQ σ q.bv x.tcbState ∧ BlkIn σ q.bv x.tcbState) :
    SchedTailHyp (L := L) arI th s σ ct := by
  intro s1 σ1 a p mcp prio scv x2 scf ssl fh q sco s2 a1 σ2 G2 hs1 hst1 hp hm hpr h1 h2 h3 hD hpI hx2 hins hx hDS2
  have ect : ct = L.curW s := by
    rw [cur_thread_eq] at hct; exact (Result.ok_injective hct).symm
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hpT := hTh p hp
  have hctT : L.curW s ∈ T := ect ▸ hTh ct htcb
  -- the restart, as `restart_dstate` has it
  obtain ⟨s1', σ1', -, hs1', hst1', hS1, hDS1, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
  have e1 : s1 = s1' := Result.ok_injective (hs1.symm.trans hs1')
  subst e1
  rw [hcur, hst1] at hst1'
  have e2 : σ1 = σ1' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hst1'))).2
  subst e2
  rw [ect] at hs1
  obtain ⟨hb1, -, est1, hk1, -, -, hid1, hac1, hy1, hc1⟩ :=
    sched.set_thread_state.restart_ok (Es := EH H) hb hctT hnb hnr hs1
  have hblk := sched.set_thread_state.restart_blk (Es := EH H) s (L.curW s) hb hctT hnb hnr
  rw [hs1, WP.spec_ok] at hblk
  obtain ⟨-, -, -, k⟩ := hblk
  have hcur1 := (restart_hB (Es := EH H) s hb hnb hnr hcurC s1 hs1).2.2.2 p
  have hK1 : KWOut (st := st) th T Cs Sg Scs Z (EH H) s1 := KWOut.ksb hK hk1
  -- the decoder's facts on the FL4 side
  have hbind1 : scf = true → scv ≠ 0#u64 → scv ∈ Scs ∧ L.mem s1 (scA p) = 0#u64 ∧
      L.mem s1 (scTcbA scv) = 0#u64 ∧ (BlockedR (L.mem s1 (P1.stA p)) → scv ∈ Ac) := by
    intro hf h0
    have hsco : sco = some (some scv.bv) := by
      cases sco with
      | none => exact absurd (h1.1 rfl) (by simp [hf])
      | some o =>
        cases o with
        | none => exact absurd (h2 rfl) h0
        | some v => rw [(h3 v rfl).1]
    obtain ⟨x, hkx, -, hB⟩ := hD
    obtain ⟨hx0, y, n, hky, hyt, hrel⟩ := hB _ hsco
    obtain ⟨hscs, hstc, hac⟩ := hRS scv y n h0 hky
    obtain ⟨hsa, hbl⟩ := hRT p x hp hkx
    refine ⟨hscs, by rw [(hy1 p hpT).2]; exact hsa hx0, by rw [(hc1 scv hscs)]; exact hstc hyt, fun hbr => ?_⟩
    by_cases e : p = L.curW s
    · rw [e, est1] at hbr
      rcases hbr with hb' | hb'
      · exact absurd hb' not_blocked_restart
      · exact absurd hb' restart_ne.1
    · have hst : L.mem s1 (P1.stA p) = L.mem s (P1.stA p) := by
        rw [P1.stA_eq]
        exact k.fld p hpT 3328#u64 (by decide) (by decide) (by decide) (by decide) (fun e' => absurd e' e)
      rw [hst] at hbr
      exact hac (hrel (hbl hbr))
  have hunb1 : scf = true → scv = 0#u64 → L.actionW s1 ≠ p ∧ L.idleW s1 ≠ p := by
    intro _ _
    refine ⟨fun e => ?_, fun e => hpI (by rw [← e, hid1])⟩
    rcases hac1 with e' | e'
    · rw [e', hact0] at e; exact notT_small hT (by rw [← e]; decide) hpT
    · rw [e'] at e; exact notT_small hT (by rw [← e]; decide) hpT
  -- the install
  have hroot : IsSlot th (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3)) :=
    AbsSlot.isSlot ⟨p, rfl, Or.inr ⟨hp, 3, by decide, rfl⟩⟩
  have hcap1 : NullOrEp H (capV (L.mem s1) (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3))) := by
    rw [hS1.capV hroot]; exact hFh p hp
  obtain ⟨hb2, F2, ha2⟩ := inst_fl4 arI th hP hSC hDS1.1.2.2.1 hb1 p hp hcap1 (cslotAddr ssl) x2 hx2 _ a s2 a1 hins
  obtain ⟨hcur2, hbind2, hunb2⟩ := conds_caifr hT hpT F2 ha2 hcur1 hbind1 hunb1
  have hK2 : KWOut (st := st) th T Cs Sg Scs Z (EH H) s2 := KWOut.ksb hK1 F2.ksb
  -- the spec after the restart
  obtain ⟨xc, hkc, -⟩ := hDS.1.1.tcb ct htcb
  have hpc : ∀ v, sco = some (some v) → p.bv ≠ σ.curThread := by
    intro v e hpe
    rw [hcur] at hpe
    have ep := P1.eq_of_bv hpe
    obtain ⟨x, hkx, -, hB⟩ := hD
    have h0 := (hRT p x hp hkx).1 (hB v e).1
    rw [ep, ect] at h0
    exact hcurC.2.1 h0
  have hpost1 := specPost_restart hInv hkc (hrun xc hkc) hst1 hD (fun x hx => hQ p x hp hx) hpc
  -- the spec across the install
  have hpost2 : SpecPost σ1 p.bv sco → SpecPost σ2 p.bv sco := by
    intro hpost
    obtain ⟨x1, hk1', -⟩ := id hpost
    obtain ⟨c, a', hca, hCR, hg⟩ := hDS1.1.1.abs_cap (sl := (p.bv, Fl4Spec.tcbCnodeIndex 3))
      ⟨p, rfl, Or.inr ⟨hp, 3, by decide, rfl⟩⟩
    rw [getCap_tcb_three hk1'] at hg
    have ha' : x1.tcbFaultHandler = a' :=
      (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hg))).1
    have hcv : capV (L.mem s1) (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3)) = c := capV_of_capAt hca
    have hfc : x1.tcbFaultHandler = absCap c := by rw [ha', hCR.abs]
    rw [hcv] at hcap1
    rcases hcap1 with hc0 | ⟨ep, b0, b1, b2, b3, b4, hce, -⟩
    · exact hpost.sk (install_sk hk1' ssl fh (Or.inl (by rw [hfc, hc0]; rfl)) hx)
    · by_cases hfin : Fl4Spec.isFinalCap' x1.tcbFaultHandler σ1
      · exact finEpSpecHyp σ1 σ2 p.bv x1 ssl fh sco hk1' ⟨_, _, _, by rw [hfc, hce]; rfl⟩ hfin hx hpost
      · refine hpost.sk (install_sk hk1' ssl fh (Or.inr ⟨by rw [hfc, hce]; simp [absCap], c, hfc,
          by rw [hce]; simp, ?_⟩) hx)
        rw [hce]
        exact ⟨rfl, by rw [← hce, ← hfc]; exact hfin⟩
  obtain ⟨x, hk2, hA2, hQ2, -, hU2, hB2⟩ := hpost2 hpost1
  -- `set_mcpriority`, `set_priority`, the SC step
  set σa := Notif.updK σ2 p.bv (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) with hσa
  have ha : ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 := by
    show _ ∈ (Fl4Spec.threadSet (Z := Unit) _ p.bv σ2).1
    rw [Notif.threadSet_eq _ hk2]; exact Set.mem_singleton _
  have hka : σa.kheap p.bv = some (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) := by
    simp [hσa, Notif.updK]
  have hAa : Notif.ActReady σa := actReady_upd (y := { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) hA2 hk2
    rfl rfl (by simp [hσa, Notif.updK]) rfl rfl rfl
  have hQa : BlkQ σa p.bv x.tcbState := BlkQ.updTcb hk2 rfl hQ2
  obtain ⟨⟨_, σb⟩, hb⟩ := setPriority_some hka (Fl4Spec.ucast 8 prio.bv) hAa hQa
  have hv : VK σ2 σb := (presV_setMcpriority _ _ σ2 _ ha).trans (presV_setPriority _ _ σa _ hb)
  obtain ⟨σc, hc⟩ : ∃ σc, ((), σc) ∈ (scStep p.bv sco σb).1 := by
    cases sco with
    | none => exact scStep_some_none _ _
    | some o =>
      cases o with
      | some v => exact scStep_some_bind ((hB2 v rfl).after _ _ ha hb)
      | none =>
        obtain ⟨c, y, n, hcx, hks, hy⟩ := hU2 rfl
        obtain ⟨xb, hkb, -, hscb⟩ := hv.tcb _ x hk2
        exact scStep_some_unbind (hv.actReady hA2) hkb (by rw [hscb, hcx]) ((hv.sc c y n).2 hks) hy
  refine WP.spec_mono (schedTail_foot arI hA s2 a1 p mcp prio scv scf hb2 hpT hpr hcur2 hbind2 hunb2) ?_
  rintro r ⟨-, hF, hr⟩
  exact ⟨slotsSame_of_footD hP hK2 hb2.1.choose_spec.choose_spec.tcbs hb2.1.choose_spec.choose_spec.nodes hF, hr,
    σa, σb, σc, ha, hb, hc⟩

/-- **Placement hypothesis: every spec SC at a nonzero address is one of
the scheduler relation's SCs `C` and of P1's SCs `Scs`.** -/
def ScSetsHyp (C Scs : Set U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (c : U64) y n, c ≠ 0#u64 → σ.kheap c.bv = some (.schedContext y n) → c ∈ C ∧ c ∈ Scs

theorem blockedR_queued {m : U64 → U64} {t : U64} {ts : Fl4Spec.ThreadState}
    (hst : (m (Notif.tStA t)).val = Notif.tsCode ts) (hb : BlockedR (m (P1.stA t))) :
    Fl4Spec.ipcQueuedThreadState ts = true := by
  have e : Notif.tStA t = P1.stA t := rfl
  rw [e] at hst
  obtain ⟨-, -, h3, h4, h6⟩ := Notif.tsVals
  have h5 : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
  have hv : (m (P1.stA t)).val = 3 ∨ (m (P1.stA t)).val = 4 ∨ (m (P1.stA t)).val = 5 ∨
      (m (P1.stA t)).val = 6 := by
    rcases hb with (e1 | e1 | e1) | e1 <;> rw [e1] <;> simp [h3, h4, h5, h6]
  rw [hst] at hv
  cases ts <;> simp [Notif.tsCode] at hv <;> rfl

/-- `schedTailHyp_disch`'s `hRT` from the scheduler relations. -/
theorem hRT_of (th : TypedHeap) {N Tr C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N Tr C c s σ) (hR : Notif.NtfnStateRel N Tr (L.mem s) σ)
    (hTr : ∀ t, th t = some .tcb → t ∈ Tr) :
    ∀ q x, th q = some .tcb → σ.kheap q.bv = some (.tcb x) →
      (x.tcbSchedContext = none → L.mem s (scA q) = 0#u64) ∧
      (BlockedR (L.mem s (P1.stA q)) → Fl4Spec.ipcQueuedThreadState x.tcbState = true) := by
  intro q x hq hk
  obtain ⟨Q, R', -, hsL⟩ := hS.lists
  obtain ⟨x', hk', -, -, hxts, -⟩ := hsL.tcb q (hTr q hq)
  rw [hk] at hk'; cases hk'
  refine ⟨fun h0 => ?_, blockedR_queued (hR.at_tcb (hTr q hq) hk).st⟩
  by_contra hne
  rw [Notif.optRef_ne hne, h0] at hxts; cases hxts

/-- `schedTailHyp_disch`'s `hRS` from the scheduler relation, P1's `SCsOK`
and `ScSetsHyp`. -/
theorem hRS_of {N Tr C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N Tr C c s σ) (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : ScSetsHyp C Scs σ) :
    ∀ (c : U64) y n, c ≠ 0#u64 → σ.kheap c.bv = some (.schedContext y n) →
      c ∈ Scs ∧ (y.scTcb = none → L.mem s (scTcbA c) = 0#u64) ∧
      (Fl4Spec.scReleased σ.curTime y = true → c ∈ Ac) := by
  intro c' y n hc0 hk
  obtain ⟨hC, hScs⟩ := hG c' y n hc0 hk
  obtain ⟨Q, R', -, hsL⟩ := hS.lists
  obtain ⟨y', n', hk', hx⟩ := hsL.scs c' hC
  rw [hk] at hk'; cases hk'
  refine ⟨hScs, fun h0 => ?_, fun hr => ?_⟩
  · rw [scTcbA_eq]
    by_contra hne
    have := hx.tcb
    rw [Notif.optRef_ne hne, h0] at this; cases this
  · have ha : 0 < y.scRefillMax := by
      simp only [Fl4Spec.scReleased, Bool.and_eq_true, Fl4Spec.scActive, Fl4Spec.activeSc,
        decide_eq_true_eq] at hr
      exact hr.1
    refine (hb.2.2.2.1.act c' hScs).2 fun e => ?_
    have := hx.max
    rw [e] at this; simp at this; omega

/-- **`tcb::decode` at `TCBSetSchedParams` end to end**
(`tcb_set_sched_params_refines` with `SchedTailHyp` by
`schedTailHyp_disch`). -/
theorem tcb_set_sched_params_refines_disch [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (th : TypedHeap) (hP : Placed th)
    (hT : TcHyps (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSchedParams)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (hpI : p ≠ L.idleW s)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    {N Tr C : Set U64} {c : U64} (hS : SchedRel st N Tr C c s σ) (hR : Notif.NtfnStateRel N Tr (L.mem s) σ)
    (hpT : p ∈ Tr) (hM : McpRel Tr (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Tr)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ C) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hnb : ¬ Blocked (L.mem s (P1.stA (L.curW s)))) (hnr : L.mem s (P1.stA (L.curW s)) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hcurC : (L.mem s (inqA (L.curW s)) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA (L.curW s)) ≠ 0#u64 ∧
      L.mem s (scA (L.curW s)) ∈ Ac)
    (hTh : ∀ t, th t = some .tcb → t ∈ T) (hK : KWOut (st := st) th T Cs Sg Scs Z (EH H) s)
    (hSC : SlotCapW th T Ω Sg) (hFh : FhSlotHyp (L := L) th H s) (hact0 : L.actionW s = 0#u64)
    (hTr : ∀ t, th t = some .tcb → t ∈ Tr) (hG : ScSetsHyp C Scs σ)
    (hInv : Inv σ) (hrun : ∀ xc, σ.kheap ct.bv = some (.tcb xc) → Fl4Spec.runnable xc.tcbState = true)
    (hQ : ∀ q x, th q = some .tcb → σ.kheap q.bv = some (.tcb x) →
      BlkQ σ q.bv x.tcbState ∧ BlkIn σ q.bv x.tcbState)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetSchedParams p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci ssl excaps buffer :=
  tcb_set_sched_params_refines arI th hP hT s ar σ G hDS hFR p hp slbl hlbl length buf ct hct args hlen hargs
    hcur htcb hact hpI hstall call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hX hS hR hpT hM hcapT hcapC hC0
    (schedTailHyp_disch arI hA th hP s σ G hDS ct hct hcur htcb hact hb hnb hnr hcurC hTh hK hSC hFh hact0
      (hRT_of th hS hR hTr) (hRS_of hS hb hG) hInv hrun hQ) blk don ci buffer

end

end

end Fl4Proofs.P3.Sched
