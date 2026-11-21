/-
P3 (DESIGN.md §9), IPC: **`send_signal` on `JAtZ`** (toward `SignalJHyp`,
ScFireJ), by the notification's state.

* `JAtZ.signal_badgeJ`: the branches that only write the notification (active:
  the badges or'ed; idle and unbound, or bound to a thread not receiving and
  not `RunningVM`: active with the badge). FL4's side is IpcNtfnSend's
  (`SingleRelI`: `IpcRel` after, the writes in the notification's words,
  `NtfnStep`), `SRT` kept (`IpcSchedHyps.stableN`'s argument); `XTopAt` by
  `XTopAt.irel_same` (the slots kept: `NWrite.iwords`); the spec's frame `NFr
  true` (the notification's object non-waiting before and after, `NObj`);
  `JRest` as `finNtfnJ`'s from `FinW` (`NWrite.finW`); P1's `BlkOK` by
  `send_signal.tinv`.
* `JAtZ.wake_post`: a waiting notification's head woken without SC
  donation: FL4's side on `IRel` with the footprint `FinStep` and the slots
  kept (`send_signal_wait_irel`, IpcSignalWake), `XTopAt` by
  `XTopAt.irel_same`, the spec's frame `NFr false` (the dequeue, then
  `wake_spec`, IpcSignalWakeSpec: the woken thread `running` with its badge
  register, `TChg`) and its scheduler invariants (`Inv`, `BlockedScActive`,
  `ActIdle`, `CurInv` unless `choose_new_thread`, `CurRunM`), `JRest` as
  `finNtfnJ`'s; P1's `BlkOK` and footprint by `send_signal.tinvF`.
* The idle notification bound to a thread blocked receiving, without SC
  donation: `JAtZ.signal_boundJ` (ScSignalBoundJ: its `cancel_ipc`, then the
  wake, in the frame `CFr`), with `RecvReplyHyp` (`recvReplyHyp_holds`).
* The wakes with an SC donation (the woken thread given the notification's
  SC, the thread having none and the SC bound to no thread:
  `schedContextDonate`/`Resume`), for a waiting notification's head or a
  bound thread blocked receiving: `JAtZ.signal_waitDJ`, `JAtZ.signal_boundDJ`
  (ScSignalDonJ, in the frame `DWFr`; the donated SC may be the current SC,
  the woken thread then owning it, `CurOwnT`), with the platform's
  `MIN_BUDGET` [P].
* `SignalRestJHyp` [J]: the remaining branch, the bound thread `RunningVM`
  (FL4's remote stall; VT-x, outside the spec model, DESIGN §5, as
  `JVtHyps`).
* `signalJHyp_of`: `SignalJHyp` from `SignalRestJHyp`, `RecvReplyHyp`,
  `MIN_BUDGET` and P1's `ArchTotal`; `jat_scheduleS`: `jat_scheduleF` with
  it.
-/
import Fl4Proofs.P3.ScFireJ
import Fl4Proofs.P3.IpcSignalWake
import Fl4Proofs.P3.ScSignalDonJ
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **A badge-only signal keeps `JAtZ`** (module docstring): the spec's
outcome `updK σ n (.notification y)`, `y` the notification with a non-waiting
object (it was non-waiting), FL4's side `SingleRelI` at that outcome. -/
theorem JAtZ.signal_badge_post {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N)
    {x y : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hxw : ∀ l, x.ntfnObj ≠ .waitingNtfn l) (hyw : ∀ l, y.ntfnObj ≠ .waitingNtfn l)
    (hyb : y.ntfnBoundTcb = x.ntfnBoundTcb) (hys : y.ntfnSc = x.ntfnSc)
    {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hspec : spec = ({((), updK σ n.bv (.notification y))}, False))
    {s' : S} (hrel : SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ spec s')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s') :
    ∃ (σ' : Fl4Spec.State Unit) (V' : XVs), spec = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
  obtain ⟨σ3, hsp, hIR3, hNS, hW, -⟩ := hrel
  have e3 : σ3 = updK σ n.bv (.notification y) := by
    have h1 := (Prod.mk.inj (hsp.symm.trans hspec)).1
    exact congrArg Prod.snd (Set.singleton_injective h1)
  subst e3
  set σ3 := updK σ n.bv (.notification y) with hσ3
  -- the spec's frame
  have hN : NObj x.ntfnObj y.ntfnObj := Or.inr ⟨hxw, hyw⟩
  have F : NFr true n.bv σ σ3 := NFr.upd hk (Or.inr (Or.inr ⟨x, y, rfl, rfl, rfl, hN.queue, fun _ => hN,
    Or.inl hys, fun _ => hN, Or.inl hyb⟩))
  have hI3 : Inv σ3 := J.inv.updNtfn hk fun p hp => J.inv.ntfnSc n.bv x p hk (hys ▸ hp)
  -- FL4's side: `IRel` after
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT := hS.placed.tcb
  have h := hI.2
  have hSRT : SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c) s' σ3 :=
    ⟨h.1.stableN h.2.1.placed hW hNS, h.2.1.stable hW hNS, h.2.2.mono hW.1 (SzKeep.ntfnStep hNS)⟩
  have hI3' : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ3 := ⟨hIR3, hSRT⟩
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ3 := hSRT.2.1
  have hks : L.ksb s' = L.ksb s := hW.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    slotsSame_of_iw J.xtop.rel.1 J.xtop.rel.2.2.2.2.2.1 J.xtop.rel.2.2.2.2.2.2 hW
      fun b hb => Or.inl (NWrite.iwords hT hb)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3' hAR hSS F.sk.cdt F.sk.orig F.ksub hks
  have hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hW.mono fun b hb => NWrite.finW hT hb
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hw
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  -- core 0's debug word: no notification or TCB word
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk 0#u64 J.kern.cs0
    have hv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp)
    have hd88 : layout.node.DEBUG_TCBS.val = 88 := P1.debug_val
    refine hW.mem_eq J.kern.dwAl fun hb => ?_
    rcases NWrite.iwords (E := Z.E) (R := Z.R) (B := Z.B) hT hb with ⟨t, ht, g1, g2⟩ | ⟨e, he, g1, g2⟩ |
      ⟨r, hr, g1, g2⟩ | ⟨m, hm, g1, g2⟩ | ⟨wp, hwp, g1, g2⟩
    · have := J.kern.hnd t _ (J.zH.1 t ht) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd e _ (J.zH.2.1 e he) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd r _ (J.zH.2.2.1 r hr) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd m _ (J.zH.2.2.2 m hm) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.nodeB wp hwp 0#u64 (by simp); omega
  -- the scheduler fields
  have hAI3 : ActIdle σ3 := F.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_nfr F hS3 hIR3 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ3 := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.finW_irq hw) (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ3 :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hSS hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.finW_utc hw hSS F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, hI3,
      J.cur.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curInv, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa, F.isorted J.isorted,
      J.curRun.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curRunW, hblk⟩
  have hC0 := JCs.same J hSS F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ3 := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
    dbgKeep_of_writes J.blk hW fun b hb => J.nwrite_notDbg hb
  exact ⟨σ3, Z.vs, hspec, rfl, J.cs_frameI hks hX3 hw (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) F.szKeep hSS F.kback F.ipcFr hC R
    hKd F.sk.orig (XTopAt.idleW_eqS J.xtop hX3 F.sk.idle) J.zD⟩

set_option maxHeartbeats 8000000 in
/-- **A waking signal keeps `JAtZ`** (module docstring): FL4's side on `IRel`
with the footprint `FinStep` and the slots kept (`IFrame`), the spec's frame
`NFr false` and its scheduler invariants given; `JRest` as `finNtfnJ`'s. -/
theorem JAtZ.wake_post {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} {s' : S} {σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hFS : FinStep (st := st) Z.T Z.N Z.C Z.c s σ s' σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : NFr false n.bv σ σ') (I3 : Inv σ') (B3 : BlockedScActive σ') (hAI3 : ActIdle σ')
    (hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') (hrun3 : CurRunM σ') :
    ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  have hw := hFS.1
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hw
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_nfr F hS3 hIR.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.finW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.finW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, B3, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩

variable (arI) in
/-- **The remote `RunningVM` signal on `JAtZ`** [J] (module docstring):
`SignalJHyp`'s statement where `send_signal` finds the idle notification's
bound thread `RunningVM` (FL4's remote stall; VT-x, outside the spec model,
DESIGN §5, as `JVtHyps`). The waking cases (a waiting notification's head,
the bound thread blocked receiving, donating the notification's SC or not)
are proved (`JAtZ.signal_waitDJ`, `JAtZ.signal_boundDJ`, ScSignalDonJ). -/
def SignalRestJHyp (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (n badge : U64) (x : Fl4Spec.Notification), JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → n ∈ Z.N →
    σ.kheap n.bv = some (.notification x) →
    (x.ntfnObj = .idleNtfn ∧ ∃ t tcb, x.ntfnBoundTcb = some t ∧
      σ.kheap t = some (.tcb tcb) ∧ tcb.tcbState = .runningVM) →
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄

set_option maxHeartbeats 8000000 in
/-- **`SignalJHyp` from the waking signals' premise** (module docstring). -/
theorem signalJHyp_of (hAT : P0.ArchTotal arI) (hW : SignalRestJHyp (L := L) arI AR H Cs)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    SignalJHyp (L := L) arI AR H Cs := by
  intro Z Ac Lst D s a σ n badge J hn
  obtain ⟨x, hk, hx⟩ := J.xtop.ipc.toN.ntfn n hn
  have hNt : ∀ m ∈ P1.Heap.ntfns H, H m = some .ntfn := fun _ h => h
  have hnH : n ∈ P1.Heap.ntfns H := J.zH.2.2.2 n hn
  have hP1 := P1.notification.send_signal.tinv hAT s a n badge J.blk hnH (hNt n hnH)
  -- the badge-only branches
  have post : ∀ (y : Fl4Spec.Notification), (∀ l, x.ntfnObj ≠ .waitingNtfn l) → (∀ l, y.ntfnObj ≠ .waitingNtfn l) →
      y.ntfnBoundTcb = x.ntfnBoundTcb → y.ntfnSc = x.ntfnSc →
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), updK σ n.bv (.notification y))}, False) →
      notification.send_signal st arI s a n badge ⦃ r => r.2 = a ∧
        SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ →
      notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
        (Lst' : U64 → List U64) (D' : Set U64),
        Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
    intro y hxw hyw hyb hys hspec hI
    refine WP.spec_mono (WP.spec_and hI hP1) ?_
    rintro ⟨s', a'⟩ ⟨⟨ea, hrel⟩, hb⟩
    try simp only [WP.uncurry'_pair] at hb
    subst ea
    obtain ⟨σ', V', h1, h2, J'⟩ := J.signal_badge_post hn hk hxw hyw hyb hys hspec hrel hb
    exact ⟨σ', V', Ac, Lst, D, h1, h2, J'⟩
  have hI := J.xtop.irelK J.ks J.buf
  cases ho : x.ntfnObj with
  | activeNtfn b0 =>
    exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn (Fl4Spec.combineNtfnBadges badge.bv b0)) x)
      (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
      (sendSignal_active_eq hk ho badge.bv) (send_signal_activeI (ar := arI) J.ip s a σ hI.1 hn hk ho badge)
  | waitingNtfn l =>
    exact J.signal_waitDJ hAT hmb hn hk ho badge
  | idleNtfn =>
    cases hb : x.ntfnBoundTcb with
    | none =>
      exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn badge.bv) x)
        (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
        (sendSignal_activate hk ho (Or.inl hb) badge.bv)
        (send_signal_idle_unboundI (ar := arI) J.ip s a σ hI.1 hn hk ho hb badge)
    | some t =>
      obtain ⟨hb0, hbt⟩ := Notif.optRef_some (hx.bound ▸ hb)
      obtain ⟨tcb, hkt, -⟩ := hI.1.tcb _ (hx.bound_mem hb0)
      rw [hbt] at hkt
      by_cases hrb : Fl4Spec.receiveBlocked tcb.tcbState = true
      · exact J.signal_boundDJ hAT hmb hn hk ho (t := L.mem s (nBoundA n)) (by rw [hbt]; exact hb)
          (by rw [hbt]; exact hkt) hrb
          badge
      by_cases hvm : tcb.tcbState = .runningVM
      · exact hW Z Ac Lst D s a σ n badge x J hn hk ⟨ho, t, tcb, hb, hkt, hvm⟩
      have hrb' : Fl4Spec.receiveBlocked tcb.tcbState = false := by simpa using hrb
      exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn badge.bv) x)
        (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
        (sendSignal_activate hk ho (Or.inr ⟨t, tcb, hb, hkt, hrb'⟩) badge.bv)
        (send_signal_idle_bound_idleI (ar := arI) J.ip s a σ hI.1 hn hk ho hb hkt hrb' hvm badge)


/-- **`jat_scheduleF` with `SignalJHyp` reduced to the waking signals**
(`signalJHyp_of`). -/
theorem jat_scheduleS {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hW : SignalRestJHyp (L := L) arI AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSw st arI Z.N Z.T Z.C Z.c)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFoot st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ∧
        CurInv σ' ⦄ :=
  jat_scheduleF s a σ J hd hnd hAT hVt (signalJHyp_of hAT hW hmb) hA hsni hsend hT hTail

end

end

end Fl4Proofs.P3
