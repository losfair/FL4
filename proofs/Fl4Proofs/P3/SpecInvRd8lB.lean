/-
P3 (DESIGN.md §9), invariant line G1 (rd8l, KENTRY-PLAN rd8k handoff 1):
**the invocation shell keeps `BlockedScActive`** (spec side only, outside the
JAtZ cone).

* **`SJ C I D s`** (the shell's carried bundle): rd8k's `KD I` (BSA,
  IdleScOutV, idleSc), sb2's `ScInv`, `CBa C`, `ct = C`, vfh's `VfC`
  (VfhAll in view form ∧ CnDom), and `Bd C` when `D` (the perform's
  non-call donation).
* `bd_sv`, `svs_of_kz`, `WS` (SVS ∧ ct kept), **`sj_of` / `sje_of`**: one
  combinator from the six families (ba_ / sb_ / uk_ / isk_ / rd12b's KZ or
  SVS ∧ cfS / vfc). Instances `sj_getMessageInfo`, `sj_invF`, `sj_getMrs`,
  `sj_setThreadState`.
* **`ba_fl4HandleInvocationR rep calling blocking don fp cptr I σ (hJ : SJ
  σ.curThread I (calling = false ∧ don = true) σ)`**: every outcome has BSA.
  rd12b's `fl4HandleInvocationR_eq` (`invF` / `invE` / `invFin`) with ctq's
  `P17.syscall_r`: the fault branch by rd8i's `ba_handleFault_p` (TA ct =
  `ta_of_fwd`), the error reply by `ba_auto`, the perform by rd8k's
  `ba_fl4PerformInvocation` with `PerfB` from rd8l's `perfB_perform` (RNE at
  the decode state, KD / VfhAll at the Restart state), the post by `ba_auto`.
-/
import Fl4Proofs.P3.SpecInvRd8lA
import Fl4Proofs.P3.SpecInvRd12bA
import Fl4Proofs.P3.SpecInvVfhE
open Classical

namespace Fl4Proofs.P3.SInvR.B8l
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif
  Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g Fl4Proofs.P3.SInvR.B8i Fl4Proofs.P3.SInvR.B8k

noncomputable section

set_option maxHeartbeats 1000000

/-- **The shell's carried bundle** (module docstring). -/
def SJ (C I : ObjRef) (D : Prop) (s : State Unit) : Prop :=
  KD I s ∧ SInvB.ScInv s ∧ CBa C s ∧ s.curThread = C ∧ SInv.VfC s ∧ (D → Bd C s)

theorem bd_sv {t : ObjRef} {s s' : State Unit} (h : Bd t s) (hs : SVK.SVS s s') : Bd t s' := by
  obtain ⟨x, c, hx, hc⟩ := h
  have e := hs.1 t
  rw [hx] at e
  obtain ⟨x', hx', e'⟩ := SVK.sv_tcb (o := s'.kheap t) (a := x.tcbSchedContext) e
  exact ⟨x', c, hx', e'.trans hc⟩

theorem svs_of_kz {σ0 s : State Unit} (h : A12b.KZ σ0 s) : SVK.SVS σ0 s := by
  obtain ⟨-, -, hc, ha⟩ := A12b.kz_parts h
  exact ⟨fun p => A12b.kz_sv h p, congrArg (fun x => x.2.2.2.2.2) hc, Or.inl ha⟩

/-- The shell's step frame: SVS and the current thread kept. -/
def WS (s s' : State Unit) : Prop := SVK.SVS s s' ∧ s'.curThread = s.curThread

theorem ws_of_kz {α : Type} {m : NonDet (State Unit) α} (h : ∀ V, IK (A12b.KZ V) m) :
    ∀ s y, y ∈ (m s).1 → WS s y.2 := fun s y hy =>
  ⟨svs_of_kz (h s s rfl y hy), A12b.kz_curThread (h s s rfl y hy)⟩

variable {C I : ObjRef} {D : Prop}

/-- **`SJ` from the six families.** -/
theorem sj_of {α : Type} {m : NonDet (State Unit) α} (hB : BAK m) (hS : ∀ h0, SInvB.SBK h0 m)
    (hU : ∀ v, SInvU.UK v m) (hN : ∀ N, SInvL.IsK N m) (hW : ∀ s y, y ∈ (m s).1 → WS s y.2)
    (hV : IK SInv.VfC m) : IK (SJ C I D) m := by
  intro s hs y hy
  obtain ⟨⟨hb, ho, hi⟩, hI, hC, hct, hv, hd⟩ := hs
  obtain ⟨hw, hc⟩ := hW s y hy
  exact ⟨⟨hB s hb y hy, SInvU.io_of_uk hU s ho y hy, hN I s hi y hy⟩, SInvB.sik_of_sbk hS s hI y hy,
    cba_sv hC hw, hc.trans hct, hV s hv y hy, fun d => bd_sv (hd d) hw⟩

theorem sje_of {ε α : Type} {m : NonDetE (State Unit) ε α} (hB : BAKE m) (hS : ∀ h0, SInvB.SBKE h0 m)
    (hU : ∀ v, SInvU.UKE v m) (hN : ∀ N, SInvL.IsKE N m) (hW : ∀ s y, y ∈ ((ExceptT.run m) s).1 → WS s y.2)
    (hV : IKE SInv.VfC m) : IKE (SJ C I D) m :=
  sj_of hB hS hU hN hW hV

theorem sj_getMessageInfo (t : ObjRef) : IK (SJ C I D) (getMessageInfo (Z := Unit) t) :=
  sj_of (by ba_auto) (fun _ => by sb_auto) (fun _ => by uk_auto) (fun _ => by isk_auto)
    (ws_of_kz fun V => A12b.kz_getMessageInfo (V := V) t) (by vfc_auto)

theorem sj_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : IKE (SJ C I D) (A12b.invF t cptr info) :=
  sje_of (by unfold A12b.invF; ba_auto) (fun _ => by unfold A12b.invF; sb_auto)
    (fun _ => by unfold A12b.invF; uk_auto) (fun _ => by unfold A12b.invF; isk_auto)
    (ws_of_kz fun V => A12b.kz_invF (V := V) t cptr info) (by unfold A12b.invF; vfc_auto)

theorem sj_getMrs (t : ObjRef) (buf : Option ObjRef) (info : MessageInfo) :
    IK (SJ C I D) (getMrs (Z := Unit) t buf info) :=
  sj_of (by ba_auto) (fun _ => by sb_auto) (fun _ => by uk_auto) (fun _ => by isk_auto)
    (ws_of_kz fun V => A12b.kz_getMrs (V := V) t buf info) (by vfc_auto)

theorem sj_setThreadState (t : ObjRef) (ts : ThreadState) (h : ipcQueuedThreadState ts = false) :
    IK (SJ C I D) (setThreadState (Z := Unit) t ts) :=
  sj_of (ba_setThreadState t ts h) (fun _ => SInvB.sb_setThreadState t ts) (fun _ => SInvU.uk_setThreadState t ts)
    (fun _ => SInvL.isk_setThreadState t ts)
    (fun s y hy => ⟨SVK.sv_setThreadState' t ts s y hy, congrArg (fun x => x.2.2.1) (cfk_setThreadState' t ts s y hy)⟩)
    (by vfc_auto)

/-! ## The shell -/

set_option maxHeartbeats 4000000 in
/-- **The invocation shell keeps `BlockedScActive`** from `SJ` at its start. -/
theorem ba_fl4HandleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) (I : ObjRef) (σ : State Unit)
    (hJ : SJ σ.curThread I (calling = false ∧ don = true) σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr).run σ).1, BSA y.2 := by
  rw [A12b.fl4HandleInvocationR_eq]
  intro y hy
  obtain ⟨z, hz1, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz1; cases he
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz1
  obtain rfl := mem_gets hw
  simp only [Except.ok.injEq] at ha; subst ha
  obtain ⟨z, hz2, ⟨info, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · unfold withoutPreemption at hz2; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz2; cases he
  unfold withoutPreemption at hz2
  obtain ⟨w0, hw0, rfl⟩ := ft_mem_liftE hz2
  simp only [Except.ok.injEq] at ha; subst ha
  have hJ0 : SJ σ.curThread I (calling = false ∧ don = true) w0.2 := sj_getMessageInfo _ σ hJ w0 hw0
  refine P17.syscall_r (I := SJ σ.curThread I (calling = false ∧ don = true)) (Q := fun y => BSA y.2)
    (fun v hv => sj_invF _ _ _ w0.2 hJ0 v hv) ?_ ?_ ?_ ?_ y hy
  · -- the fault branch
    intro f s hs v hv
    show BSA v.2
    unfold NonDet.when at hv
    split at hv
    · exact ba_handleFault_p σ.curThread f s (ta_of_fwd hs.2.1.fwd hs.2.2.1) hs.2.2.1 hs.1.1 v hv
    · rw [Set.mem_singleton_iff.1 hv]; exact hs.1.1
  · -- the decode
    intro a s hs w hw
    have hJs := sj_invF (C := σ.curThread) (I := I) (D := calling = false ∧ don = true) _ _ _ w0.2 hJ0 _ hs
    obtain ⟨sl, cap, ex, buf⟩ := a
    unfold A12b.invE at hw
    obtain ⟨z, hz, ⟨args, ha', hd⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hw
    · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz
      have hJx := sj_getMrs _ _ _ s hJs x hx
      exact (sje_of (by ba_auto) (fun _ => by sb_auto) (fun _ => by uk_auto) (fun _ => by isk_auto)
        (ws_of_kz fun V => A12b.kz_fl4DecodeInvocation (V := V) _ _ _ _ _ _ _ _) (by vfc_auto)) x.2 hJx w hd
    · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz
      exact sj_getMrs _ _ _ s hJs x hx
  · -- the error reply
    intro e s hs v hv
    exact (show BAK (NonDet.when calling (fl4ReplyFromKernelError (Z := Unit) rep σ.curThread
      (msgFromSyscallError e))) by ba_auto) s hs.1.1 v hv
  · -- the finalise phase
    intro a s b s' has hbs hs' y hy
    have hJs := sj_invF (C := σ.curThread) (I := I) (D := calling = false ∧ don = true) _ _ _ w0.2 hJ0 _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    unfold A12b.invE at hbs
    obtain ⟨z, hz, ⟨args, ha', hd⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hbs
    swap
    · cases (Prod.mk.inj he).1
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz
    simp only [Except.ok.injEq] at ha'; subst ha'
    have hJx := sj_getMrs (C := σ.curThread) (I := I) (D := calling = false ∧ don = true) _ _ _ s hJs x hx
    have hN : SInvB.RNE x.2 := hJx.2.1.2
    unfold A12b.invFin at hy
    obtain ⟨z1, hz1, ⟨u1, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
    swap
    · unfold withoutPreemption at hz1; obtain ⟨w, -, hw⟩ := SInvU.mem_liftE' hz1; rw [hw] at he; cases he
    unfold withoutPreemption at hz1
    obtain ⟨w1, hw1, rfl⟩ := SInvU.mem_liftE' hz1
    have hJ1 := sj_setThreadState (C := σ.curThread) (I := I) (D := calling = false ∧ don = true)
      σ.curThread .restart rfl s' hs' w1 hw1
    obtain ⟨hK1, hI1, hC1, hct1, hv1, hd1⟩ := hJ1
    have hVf : VfhAll w1.2 := (SInv.vfhV_iff _).1 hv1.1
    have hP := ba_fl4PerformInvocation blocking calling don b I w1.2 hK1 hI1 (by rw [hct1]; exact hC1)
      (fun c d => by rw [hct1]; exact hd1 ⟨c, d⟩) (perfB_perform hN hd σ.curThread hw1 hK1 hVf)
    obtain ⟨z2, hz2, ⟨r2, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · exact (show IKE BSA _ by unfold withoutPreemption; refine ike_liftE ?_; ba_auto) z2.2 (hP z2 hz2) y hy
    · exact hP z2 hz2

end

end Fl4Proofs.P3.SInvR.B8l
