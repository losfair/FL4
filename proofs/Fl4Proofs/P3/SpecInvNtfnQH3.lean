/-
P3 (DESIGN.md §9), invariant line G1 (nq1, nq2): **NtfnQB and EpQB kept by
the syscall entry and every kernel event** (spec side only).

* Shell invariant `Iu ct`: `NQ [ct]` (ct in no queue, not BlockedOnNotification),
  ct current, ut1's `UtInv` and the [J] fact `NqDet` (both read only by the
  untyped / MakePool performs, carried by the front end and decode as frames:
  `iu_of` = the NQ family, the current-thread frame `CTK`, ft2's generic frame
  with `fqB` (no TCB of a childless untyped's region becomes IPC-blocked) and
  ut1's view frame `UK`).
* The decode's facts (`NqDec`: an untyped retype passed the decode's checks,
  `SInvU.UtRetOK`; a MakePool's parent is a childless page-sized untyped at
  the frame) are proved (`nqDecW`, nq2) from ut3's `okv_fl4Decode` (SpecInvUtDA)
  — no premise.
* nq3: the send phase of ReplyRecv / NBSendRecv / NBSendWait does not block,
  so `handle_invocation` keeps the current thread in no queue (`NqI`): the
  current thread is Restart during `perform_invocation` (`PJ [ct]`), so it is
  neither a reply's receiver nor moved by `set_priority`.
* Tops: `kentry_ntfnQB`, `kcall_ntfnQB` for every syscall and every event;
  `ctEntry_of` turns "ct active" into ft3's `CtEntry`.
-/
import Fl4Proofs.P3.SpecInvNtfnQH2
import Fl4Proofs.P3.SpecInvNtfnQC4
import Fl4Proofs.P3.SpecInvUtDA
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The shell invariant -/

/-- The syscall shell's invariant at the current thread `ct`. -/
def Iu (ct : ObjRef) (s : State Unit) : Prop :=
  NQ [ct] s ∧ s.curThread = ct ∧ SInvU.UtInv s ∧ NqDet s

/-- At the TCBs of `X`: not IPC-blocked (closed under the writes of ft2's generic frame). -/
def fqB (X : Set ObjRef) : FQ where
  R p _ s := p ∈ X → ¬ ipcBlk s
  clr _ _ _ h := h
  st _ _ _ _ _ h := h.elim (fun h => h) (fun h => h rfl)
  dflt _ _ h := h.elim (fun h => h) (fun h => h rfl)

/-- The regions of the childless untyped caps. -/
def detX (σ : State Unit) : Set ObjRef :=
  {t | ∃ u dev b n fi, SInvU.capAt σ u = some (.untypedCap dev b n fi) ∧ (∀ c, σ.cdt c ≠ some u) ∧
    t ∈ SInvU.delR b n}

theorem opg_of_nqDet {σ : State Unit} (hD : NqDet σ) : OPG (fqB (detX σ)) Set.univ (fun _ => True) σ := by
  refine ⟨fun p o hp => ?_, trivial⟩
  cases o with
  | tcb x =>
    rintro ⟨u, dev, b, n, fi, hc, hk, hm⟩
    exact hD u dev b n fi hc hk p hm x hp
  | notification n => exact fun t _ => Set.mem_univ _
  | _ => trivial

theorem nqDet_of {σ σ' : State Unit} (h : SInvU.uV σ' = SInvU.uV σ)
    (hg : OPG (fqB (detX σ)) Set.univ (fun _ => True) σ') : NqDet σ' := by
  have hcap : SInvU.capAt σ' = SInvU.capAt σ := congrArg (fun w : SInvU.UView => w.2.1) h
  have hcdt : σ'.cdt = σ.cdt := congrArg (fun w : SInvU.UView => w.2.2.1) h
  intro u dev b n fi hc hk t ht y hy
  exact hg.1 t _ hy ⟨u, dev, b, n, fi, by rw [← hcap]; exact hc, by rw [← hcdt]; exact hk, ht⟩

/-- A frame for all four parts of `Iu`. -/
theorem iu_of {ct : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α} (hN : NQKE [ct] m) (hC : CTKE ct m)
    (hG : ∀ F S, FGKE F S (fun _ => True) m) (hU : ∀ v, SInvU.UKE v m) : IKE (Iu ct) m := by
  intro σ h y hy
  have hv : SInvU.uV y.2 = SInvU.uV σ := hU _ σ rfl y hy
  exact ⟨hN σ h.1 y hy, hC σ h.2.1 y hy, SInvU.utInv_view hv h.2.2.1,
    nqDet_of hv (hG (fqB (detX σ)) Set.univ σ (opg_of_nqDet h.2.2.2) y hy)⟩

theorem iu_ofK {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α} (hN : NQK [ct] m) (hC : CTK ct m)
    (hG : ∀ F S, FGK F S (fun _ => True) m) (hU : ∀ v, SInvU.UK v m) : IK (Iu ct) m := by
  intro σ h y hy
  have hv : SInvU.uV y.2 = SInvU.uV σ := hU _ σ rfl y hy
  exact ⟨hN σ h.1 y hy, hC σ h.2.1 y hy, SInvU.utInv_view hv h.2.2.1,
    nqDet_of hv (hG (fqB (detX σ)) Set.univ σ (opg_of_nqDet h.2.2.2) y hy)⟩

macro "iu_auto" : tactic => `(tactic| first
  | exact iu_of (by nq_auto) (by ct_auto) (fun _ _ => by fg_auto) (fun _ => by uk_auto)
  | exact iu_ofK (by nq_auto) (by ct_auto) (fun _ _ => by fg_auto) (fun _ => by uk_auto))

theorem iu_nq' {ct : ObjRef} {s : State Unit} (h : Iu ct s) : NQ [] s := nq_weak_nil _ h.1

/-- The post of `handle_invocation`: `NQ []`, and the current thread still in no
queue when the invocation does not block. -/
def NqI (ct : ObjRef) (blocking : Bool) (s : State Unit) : Prop := NQ [] s ∧ (blocking = false → NQ [ct] s)

theorem nqI_of {ct : ObjRef} {b : Bool} {s : State Unit} (h : NQ [ct] s) : NqI ct b s := ⟨nq_weak_nil _ h, fun _ => h⟩

theorem iuQ {ct : ObjRef} {b : Bool} {s : State Unit} (h : Iu ct s) : NqI ct b s := nqI_of h.1

/-- `set_thread_state t ts` with an `okSt` state: afterwards `PJ [t]`. -/
theorem pj_sts1 (t : ObjRef) (ts : ThreadState) (h : okSt ts) (σ : State Unit) :
    ∀ y ∈ (setThreadState (Z := Unit) t ts σ).1, PJ [t] y.2 := by
  intro y hy
  unfold setThreadState at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨x, hx, e⟩ := mem_threadSet h1
  have h2 : PJ [t] y1.2 := by
    rw [e]
    intro p z hp hm
    simp only [List.mem_singleton] at hm
    subst hm
    simp only [Function.update_apply, if_pos rfl] at hp
    cases hp
    exact h
  exact (show PJK [t] (setThreadStateAct (Z := Unit) t) by unfold setThreadStateAct setSchedulerAction; pj_auto)
    y1.2 h2 y hy

/-! ## The decode's facts -/

/-- The syscall front end (`handle_invocation`'s lookups). -/
def nqFront (thread : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    FMonad Unit (CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) := do
  let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
  let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
  let extracaps ← lookupExtraCaps thread buffer info
  NonDetE.returnOk (slot, cap, extracaps, buffer)

/-- The decode after the front end. -/
def nqDecode (thread : ObjRef) (firstPhase : Bool) (cptr : CapRef) (info : MessageInfo) :
    CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef → SEMonad Unit Fl4Invocation :=
  fun (slot, cap, extracaps, buffer) => do
    let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buffer info
    fl4DecodeInvocation firstPhase info.miLabel args cptr slot cap extracaps buffer

/-- The decode's facts the performs need (nq1's former [W] gap, now proved:
`nqDecW`): every invocation the front end and decode return satisfies `NqDec`
at the decode's end state. -/
def NqDecW : Prop :=
  ∀ (thread : ObjRef) (fp : Bool) (cptr : CapRef) (info : MessageInfo) (σ0 s s' : State Unit)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) (b : Fl4Invocation),
    ((.ok a, s) : Except Fault _ × State Unit) ∈ ((nqFront thread cptr info).run σ0).1 →
    ((.ok b, s') : Except SyscallError Fl4Invocation × State Unit) ∈ ((nqDecode thread fp cptr info a).run s).1 →
    NqDec s' b

theorem nqDec_of {s : State Unit} {b : Fl4Invocation} (h : SInvU.InvOKV (SInvU.uV s) b) : NqDec s b := by
  refine ⟨fun ui e => ?_, fun fr sl pa ba e => ?_⟩
  · subst e; exact SInvU.utRetOK_of_V h.1
  · subst e; exact h

/-- **The decode's facts**, from ut3's `okv_fl4Decode` (the untyped decode's
`UtRetOK`, the arch decode's MakePool checks) and the front end's lookups (the
invoked cap and the extra caps are those of their slots). -/
theorem nqDecW : NqDecW := by
  intro thread fp cptr info σ0 s s' a b has hbs
  have hOk : SInvU.OkV (SInvU.uV σ0) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (SInvU.uV σ0).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (SInvU.uV σ0).2.1 p.2 = some p.1)
      (nqFront thread cptr info) := by
    unfold nqFront
    refine SInvU.okv_bind (fun _ => SInvU.uk_capFaultOnFailure _ _ _ (SInvU.uk_lookupCapAndSlot _ _))
      (SInvU.okv_capFaultOnFailure _ _ (SInvU.okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine SInvU.okv_bind_uk (fun _ => ike_liftE (SInvU.uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine SInvU.okv_bind (fun _ => SInvU.uk_lookupExtraCaps _ _ _) (SInvU.okv_lookupExtraCaps _ _ _)
      fun ex hex => SInvU.okv_returnOk ?_
    exact ⟨hx, hex⟩
  have hvs : SInvU.uV s = SInvU.uV σ0 :=
    (show ∀ v, SInvU.UKE v (nqFront thread cptr info) from fun _ => by unfold nqFront; uk_auto) _ σ0 rfl _ has
  obtain ⟨sl, cap, ex, buf⟩ := a
  obtain ⟨hc, hex⟩ := hOk σ0 rfl _ s has
  have hdec : SInvU.InvOKV (SInvU.uV σ0) b :=
    SInvU.okv_bind_uk (P := SInvU.InvOKV (SInvU.uV σ0)) (fun _ => ike_liftE (SInvU.uk_getMrs _ _ _)) (fun args =>
      SInvU.okv_fl4Decode (w := SInvU.uV σ0) fp info.miLabel args cptr sl cap ex buf hc hex) s hvs b s' hbs
  have hv' : SInvU.uV s' = SInvU.uV σ0 :=
    ((show ∀ v, SInvU.UKE v (nqDecode thread fp cptr info (sl, cap, ex, buf)) from
      fun _ => by unfold nqDecode; uk_auto) _ s rfl _ hbs).trans hvs
  rw [← hv'] at hdec
  exact nqDec_of hdec

/-! ## `handle_invocation` -/

/-- `set_thread_state` to a state that is not IPC-blocked keeps `NqDet`. -/
theorem nqDet_sts {σ : State Unit} (t : ObjRef) (ts : ThreadState) (h : ¬ ipcBlk ts) (hD : NqDet σ)
    {y : Unit × State Unit} (hy : y ∈ (setThreadState (Z := Unit) t ts σ).1) : NqDet y.2 := by
  have hv : SInvU.uV y.2 = SInvU.uV σ :=
    (SInvU.uk_setThreadState (v := SInvU.uV σ) t ts) σ rfl y hy
  unfold setThreadState at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨x, hx, e⟩ := mem_threadSet h1
  have hk : y.2.kheap = y1.2.kheap := kh_setThreadStateAct t y1.2.kheap y1.2 rfl y hy
  refine nqDet_of hv ⟨fun p o hp => ?_, trivial⟩
  rw [hk, e] at hp
  simp only [Function.update_apply] at hp
  split_ifs at hp with hpt
  · cases hp; intro _; exact h
  · exact (opg_of_nqDet hD).1 p o hp

/-- The shell's `set_thread_state ct Restart` keeps `Iu ct`. -/
theorem iu_sts {ct : ObjRef} {σ : State Unit} (h : Iu ct σ) {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) ct .restart σ).1) : Iu ct y.2 := by
  have hv : SInvU.uV y.2 = SInvU.uV σ :=
    (SInvU.uk_setThreadState (v := SInvU.uV σ) ct .restart) σ rfl y hy
  exact ⟨nq_setThreadState ct .restart (List.mem_singleton_self _) (fun h => h) σ h.1 y hy,
    (ct_setThreadState (cq := ct) ct .restart) σ h.2.1 y hy,
    SInvU.utInv_view hv h.2.2.1,
    nqDet_sts ct .restart (by simp [ipcBlk, isBoN, epBlocked]) h.2.2.2 hy⟩


set_option maxHeartbeats 8000000 in
theorem nq_fl4HandleInvocationR (ct : ObjRef) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    HKE (Iu ct) (NqI ct blocking) (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.2.1
  simp only [hc, withoutPreemption]
  refine hke_bind (R := Iu ct) (Q := NqI ct blocking) (hk_liftE (hk_of_ik ?_)) (fun info => ?_) (fun s h => iuQ h) σ hσ
  · iu_auto
  intro σ' hσ' y0 hy0
  refine ft_syscall_post (I := Iu ct) (Q := NqI ct blocking) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · refine (?_ : IKE (Iu ct) _) σ' hσ'
    iu_auto
  · intro f s hs v hv
    unfold NonDet.when at hv
    split at hv
    · rename_i hb
      exact ⟨nq_weak_nil _ (nq_handleFault ct f (List.mem_singleton_self _) s hs.1 v hv), fun h => by simp [h] at hb⟩
    · rw [Set.mem_singleton_iff.1 hv]; exact iuQ hs
  · intro a s has w hw
    have hs : Iu ct s := by
      refine (?_ : IKE (Iu ct) _) σ' hσ' _ has
      iu_auto
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (Iu ct) _) s hs w hw
    iu_auto
  · intro e s hs v hv
    refine nqI_of ((?_ : NQK [ct] _) s hs.1 v hv)
    nq_auto
  · intro a s b s' has hbs hI y hy
    have hd : NqDec s' b := nqDecW ct fp cptr info σ' s s' a b has hbs
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
    · have hz1 : Iu ct z.2 := by
        obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
        exact iu_sts hI hw
      have hv : SInvU.uV z.2 = SInvU.uV s' := by
        refine (?_ : SInvU.UKE (ε := Unit) (SInvU.uV s') _) s' rfl z hz
        uk_auto
      have hd1 : NqDec z.2 b := nqDec_view hv hd
      have hp1 : PJ [ct] z.2 := by
        obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
        exact pj_sts1 ct .restart ⟨rfl, fun h => h⟩ s' w hw
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hpre : NQ [ct] s1 ∧ s1.curThread ∈ [ct] ∧ PJ [ct] s1 ∧ NqDec s1 b ∧ SInvU.UtInv s1 ∧ NqDet s1 :=
        ⟨hz1.1, by rw [hz1.2.1]; exact List.mem_singleton_self _, hp1, hd1, hz1.2.2.1, hz1.2.2.2⟩
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := nq_fl4PerformInvocation blocking calling don b s1 hpre _ hz2
        refine ⟨(?_ : NQKE [] _) s2 hs2.1 y hy, fun hb => (?_ : NQKE [ct] _) s2 (hs2.2 hb) y hy⟩ <;> nq2_auto
      · exact nq_fl4PerformInvocation blocking calling don b s1 hpre _ hz2
    · have hz1 : Iu ct z.2 := by
        obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
        exact iu_sts hI hw
      exact iuQ hz1

/-! ## `handle_recv` -/

set_option maxHeartbeats 8000000 in
theorem nq_handleRecv (ct : ObjRef) (blk canReply : Bool) :
    HK (fun s => NQ [ct] s ∧ s.curThread = ct) (NQ []) (handleRecv (Z := Unit) blk canReply) := by
  have hct : ct ∈ [ct] := List.mem_singleton_self _
  have hnil : ∀ s, NQ [ct] s → NQ [] s := fun s h => nq_mono h fun _ h => by cases h
  have hRIP : ∀ c rc, HK (NQ [ct]) (NQ []) (receiveIpc (Z := Unit) ct c blk rc) :=
    fun c rc => hk_post (nq_receiveIpc ct c blk rc hct) nq_weak_nil
  have hRS : ∀ c, HK (NQ [ct]) (NQ []) (receiveSignal (Z := Unit) ct c blk) := by
    intro c s hs z hz
    have := nq_receiveSignal ct c blk hct s hs z hz
    exact nq_mono this fun u hu => by simp at hu
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = ct := hσ.2
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : NQ [ct] y2.2 := (?_ : NQK [ct] _) σ hσ.1 y2 h2
  · refine hk_catch (I := NQ [ct]) (Q0 := NQ []) ?_ (fun e => ?_) y2.2 hb2 y hy
    · (try dsimp only)
      refine hkr_bind (by nq_auto) (fun epCap => ?_)
      (try dsimp only)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (by nq_auto) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
          · refine hkr_bind (by nq_auto) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
        · exact hkr_throw _
      · (try dsimp only)
        split
        · refine hkr_bind (by nq_auto) (fun bt => ?_)
          (try dsimp only)
          split
          · exact hkr_liftE (hRS _)
          · exact hkr_throw _
        · exact hkr_throw _
      · exact hkr_throw _
    · exact hk_post (nq_handleFault ct e hct) nq_weak_nil
  · nq_auto

/-! ## `handle_syscall` and the events -/

theorem hke_ct {ct : ObjRef} {ε α : Type} {P Q : State Unit → Prop} {m : NonDetE (State Unit) ε α}
    (h : HKE P Q m) (hC : CTKE ct m) :
    HKE (fun s => P s ∧ s.curThread = ct) (fun s => Q s ∧ s.curThread = ct) m :=
  fun σ hσ y hy => ⟨h σ hσ.1 y hy, hC σ hσ.2 y hy⟩

theorem iu_nq {ct : ObjRef} {s : State Unit} (h : Iu ct s) : NQ [] s := nq_mono h.1 fun _ h => by cases h

set_option maxHeartbeats 8000000 in
theorem nq_fl4HandleSyscall (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKE (Iu ct) (NQ []) (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef), HKE (Iu ct) (NQ []) (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) :=
    fun cl bl dn fp cptr => hk_post (nq_fl4HandleInvocationR ct rep cl bl dn fp cptr) fun _ h => h.1
  -- the send phase of ReplyRecv / NBSendRecv / NBSendWait does not block: the current thread stays in no queue
  have hInvNB : ∀ (cl dn fp : Bool) (cptr : CapRef), HKE (Iu ct) (fun s => NQ [ct] s ∧ s.curThread = ct)
      (fl4HandleInvocationR (Z := Unit) rep cl false dn fp cptr) :=
    fun cl dn fp cptr σ hσ y hy => ⟨(nq_fl4HandleInvocationR ct rep cl false dn fp cptr σ hσ y hy).2 rfl,
      ct_fl4HandleInvocationR (cq := ct) rep cl false dn fp cptr σ hσ.2.1 y hy⟩
  have hRecv : ∀ b r, HKE (fun s => NQ [ct] s ∧ s.curThread = ct) (NQ []) (withoutPreemption (Z := Unit) (handleRecv b r)) :=
    fun b r => hk_liftE (nq_handleRecv ct b r)
  have hSR : ∀ (reg : Register) (cl dn fp : Bool) (b r : Bool), HKE (Iu ct) (NQ []) (do
      let cptr ← withoutPreemption (Z := Unit) (getCapReg reg)
      fl4HandleInvocationR rep cl false dn fp cptr
      withoutPreemption (handleRecv b r)) := by
    intro reg cl dn fp b r
    refine hke_bind (R := Iu ct) (hk_liftE (hk_of_ik (by iu_auto))) (fun cptr => ?_) (fun s h => iu_nq h)
    exact hke_bind (hInvNB _ _ _ cptr) (fun _ => hRecv b r) (fun s h => nq_weak_nil _ h.1)
  cases c
  case sysSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Iu ct) (hk_liftE (hk_of_ik (by iu_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => iu_nq h)
  case sysNBSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Iu ct) (hk_liftE (hk_of_ik (by iu_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => iu_nq h)
  case sysCall =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Iu ct) (hk_liftE (hk_of_ik (by iu_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => iu_nq h)
  case sysYield =>
    simp only [fl4HandleSyscall]
    exact hk_liftE (hk_pre nq_handleYield fun s h => h.1)
  case sysReplyRecv => exact hSR _ _ _ _ _ _
  case sysNBSendRecv => exact hSR _ _ _ _ _ _
  case sysNBSendWait => exact hSR _ _ _ _ _ _
  all_goals
    simp only [fl4HandleSyscall]
    exact hk_pre (hRecv _ _) fun s h => ⟨h.1, h.2.1⟩

/-- `check_budget` with a `true` result leaves the state unchanged. -/
theorem checkBudget_true {σ : State Unit} {y : Bool × State Unit} (hy : y ∈ (checkBudget (Z := Unit) σ).1)
    (hr : y.1 = true) : y.2 = σ := by
  unfold checkBudget at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [mem_gets h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  have e3 : y3.2 = σ := (show IK (fun s => s = σ) (getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime) by
    repeat' (first | ik_step0 | ik_unfold)) σ rfl y3 h3
  (try dsimp only at hy)
  split at hy
  · obtain ⟨y4, h4, hy⟩ := hy
    rw [mem_gets h4] at hy
    rw [Set.mem_singleton_iff.1 hy]; exact e3
  · obtain ⟨y4, h4, hy⟩ := hy
    obtain ⟨y5, h5, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hy] at hr
    cases hr

theorem checkBudgetRestart_true {σ : State Unit} {y : Bool × State Unit}
    (hy : y ∈ (checkBudgetRestart (Z := Unit) σ).1) (hr : y.1 = true) : y.2 = σ := by
  unfold checkBudgetRestart at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [mem_gets h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h3
  obtain ⟨y4, h4, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy] at hr ⊢
  have hr' : y1.1 = true := hr
  have e1 := checkBudget_true h1 hr'
  unfold NonDet.when at h4
  rw [if_neg (by simp [hr'])] at h4
  rw [Set.mem_singleton_iff.1 h4]; exact e1

theorem nq_fl4HandleEvent_sys (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKE (Iu ct) (NQ []) (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  simp only [fl4HandleEvent]
  refine hke_bind (R := Iu ct) (hk_liftE (hk_of_ik (by iu_auto))) (fun _ => ?_) (fun s h => iu_nq h)
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    have hbw : NQ [] w.2 := nq_checkBudgetRestart σ (iu_nq hσ) w hw
    unfold NonDetE.whenE at hy
    split at hy
    · rename_i hr
      rw [checkBudgetRestart_true hw hr] at hy
      exact nq_fl4HandleSyscall ct rep c σ hσ y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hbw
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

set_option maxHeartbeats 8000000 in
/-- Every event other than a syscall: the current thread `ct` is in no queue and current. -/
theorem nq_handleEvent_other (ct : ObjRef) (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c) :
    HKE (fun s => NQ [ct] s ∧ s.curThread = ct) (NQ []) (handleEvent (Z := Unit) ev) := by
  have hnil : ∀ s, NQ [ct] s → NQ [] s := fun s h => nq_mono h fun _ h => by cases h
  have hct : ct ∈ [ct] := List.mem_singleton_self _
  -- the fault handlers run on the re-read current thread, which is `ct` (the frame `CTK`)
  have hF : ∀ (m : SMonad Unit Unit) (hm : NQK [ct] m) (hc : CTK ct m) (F : ObjRef → SMonad Unit Unit)
      (hF : ∀ s, NQ [ct] s → ∀ z ∈ (F ct s).1, NQ [] z.2),
      HK (fun s => NQ [ct] s ∧ s.curThread = ct) (NQ []) (do
        m
        let restart ← checkBudgetRestart (Z := Unit)
        NonDet.when restart <| do
          let thread ← NonDet.gets fun s : State Unit => s.curThread
          F thread) := by
    intro m hm hc F hF σ hσ y ⟨y1, h1, hy⟩
    have hb1 : NQ [ct] y1.2 := hm σ hσ.1 y1 h1
    have hc1 : y1.2.curThread = ct := hc σ hσ.2 y1 h1
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 : NQ [] y2.2 := nq_checkBudgetRestart y1.2 hb1 y2 h2
    (try dsimp only at hy)
    unfold NonDet.when at hy
    split at hy
    · rename_i hr
      have e2 : y2.2 = y1.2 := checkBudgetRestart_true h2 hr
      obtain ⟨y3, h3, hy⟩ := hy
      rw [mem_gets h3] at hy
      (try dsimp only at hy)
      rw [e2, hc1] at hy
      exact hF _ hb1 y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hb2
  have hHF : ∀ f, ∀ s, NQ [ct] s → ∀ z ∈ (handleFault (Z := Unit) ct f s).1, NQ [] z.2 :=
    fun f s hs z hz => nq_weak_nil _ (nq_handleFault ct f hct s hs z hz)
  cases ev with
  | syscallEvent c => exact absurd rfl (hev c)
  | interrupt =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE ?_
    refine hk_bind (hk_pre (hk_of_ik (by nq_auto)) fun s h => h.1) fun _ => ?_
    refine hk_bind nq_checkBudget fun _ => ?_
    exact hk_of_ik (by nq2_auto)
  | unknownSyscall n =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (hF _ (by nq_auto) (by ct_auto) _ (hHF _))
  | userLevelFault w1 w2 =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (hF _ (by nq_auto) (by ct_auto) _ (hHF _))
  | vmFaultEvent ft =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (hF _ (by nq_auto) (by ct_auto) _ ?_)
    intro s hs z hz
    exact hk_catch (I := NQ [ct]) (Q0 := NQ []) (hkr_of_ike (by nq_auto) fun _ h => nq_weak_nil _ h) (fun e => hHF e) s hs z hz
  | hypervisorEvent ht =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (hF _ (by nq_auto) (by ct_auto) _ ?_)
    intro s hs z hz
    refine nq_weak_nil _ ((?_ : NQK [ct] _) s hs z hz)
    nq2_auto

theorem nq_fl4HandleEvent_other (ct : ObjRef) (rep : Bool) (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c) :
    HKE (fun s => NQ [ct] s ∧ s.curThread = ct) (NQ []) (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (hev c)
  | _ => simp only [fl4HandleEvent]; exact nq_handleEvent_other ct _ hev

/-- `fl4CallKernel` from a handler result that is `NQ []` on both outcomes. -/
theorem nq_fl4CallKernel_of {rep : Bool} {ev : Event} {P : State Unit → Prop}
    (h : HKE P (NQ []) (fl4HandleEvent (Z := Unit) rep ev)) :
    HK P (NQ []) (fl4CallKernel (Z := Unit) rep ev) := by
  intro σ hσ y hy
  unfold fl4CallKernel at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 : NQ [] y1.2 := by
    unfold NonDetE.handleE at h1
    obtain ⟨z, hz, h1⟩ := h1
    have hz' := h σ hσ z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 h1]; exact hz'
    | error e =>
      obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) h1
      exact nq_preemptionPath s hz' w hw
  refine (?_ : NQK [] _) y1.2 hb1 y hy
  nq2_auto

/-! ## The tops -/

theorem ok_of_active {s : ThreadState} (h : activeSt s) : ¬ isBoN s ∧ epBlocked s = none := by
  revert h; cases s <;> simp [activeSt, isBoN, epBlocked]

/-- **NtfnQB and EpQB kept by the syscall entry** (`fl4KernelEntrySyscall`)
for every syscall, from an active
current thread, with ut1's `UtInv` and the [J] fact `NqDet` (the region of a
childless untyped holds no IPC-blocked thread). -/
theorem kentry_ntfnQB (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) (h : NtfnQB σ ∧ EpQB σ)
    (hU : SInvU.UtInv σ) (hD : NqDet σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, NtfnQB y.2 ∧ EpQB y.2 := by
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hI : Iu σ.curThread σ := ⟨nq_cons ((nq_nil_iff σ).2 h) fun x hx => ok_of_active (ha x hx), rfl, hU, hD⟩
  have hI2 : Iu σ.curThread y2.2 := by
    refine (?_ : IK (Iu σ.curThread) _) σ hI y2 h2
    iu_auto
  exact (nq_fl4CallKernel_of (nq_fl4HandleEvent_sys σ.curThread rep c) y2.2 hI2 y hy).1

/-- **NtfnQB and EpQB kept by every kernel event** (`fl4CallKernel rep ev`):
the current thread active (or, for
an interrupt, idle), and for a syscall event the facts of `kentry_ntfnQB`. -/
theorem kcall_ntfnQB (rep : Bool) (ev : Event) {σ : State Unit}
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) →
      activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState))
    (h : NtfnQB σ ∧ EpQB σ) (hU : SInvU.UtInv σ) (hD : NqDet σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, NtfnQB y.2 ∧ EpQB y.2 := by
  have hK : NQ [σ.curThread] σ := by
    refine nq_cons ((nq_nil_iff σ).2 h) fun x hx => ?_
    rcases ha x hx with h1 | ⟨-, h1⟩
    · exact ok_of_active h1
    · rw [h1]; exact ⟨fun h => h, rfl⟩
  intro y hy
  refine (nq_nil_iff _).1 ?_
  by_cases hs : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := hs
    exact nq_fl4CallKernel_of (nq_fl4HandleEvent_sys σ.curThread rep c) σ ⟨hK, rfl, hU, hD⟩ y hy
  · exact nq_fl4CallKernel_of (nq_fl4HandleEvent_other σ.curThread rep ev fun c e => hs ⟨c, e⟩) σ ⟨hK, rfl⟩ y hy

/-- `kentry_ntfnQB` with `NqDet` from ut4's `UtInv''` and the [J] `IfLiveB`. -/
theorem kentry_ntfnQB_live (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) (h : NtfnQB σ ∧ EpQB σ)
    (hU : SInvU.UtInv σ) (hU2 : SInvU.UtInv'' σ) (hL : IfLiveB σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, NtfnQB y.2 ∧ EpQB y.2 :=
  kentry_ntfnQB rep c ha h hU (nqDet_of_live hU2 hL)

/-- `kcall_ntfnQB` with `NqDet` from ut4's `UtInv''` and the [J] `IfLiveB`. -/
theorem kcall_ntfnQB_live (rep : Bool) (ev : Event) {σ : State Unit}
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) →
      activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState))
    (h : NtfnQB σ ∧ EpQB σ) (hU : SInvU.UtInv σ) (hU2 : SInvU.UtInv'' σ) (hL : IfLiveB σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, NtfnQB y.2 ∧ EpQB y.2 :=
  kcall_ntfnQB rep ev ha h hU (nqDet_of_live hU2 hL)

/-- The corollary for ft3's tops: NtfnQB and an active current thread give `CtEntry`. -/
theorem ctEntry_of_ntfnQB {σ : State Unit} (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (h : NtfnQB σ) : CtEntry σ := ctEntry_of ha h

end

end Fl4Proofs.P3.SInv
