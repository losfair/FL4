/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive ∧ NtfnScB across
`handle_invocation`** (sl2 handoff 4, first part; spec side only).

* `decS_nBind`: the notification-bind fact at the decode's END state (the SC
  decode reads only: `keep_decBind`; every other value carries no fact, `NBnd`).
* Shell invariant **`Js I ct d N σe s`**: sl2's `SAP I [ct] [ct] d ct` (the pin
  when `d`), nq1's `NQ [ct]`, the current thread, ut7's IRQ node, the fixed idle
  SC, and the view and binding frame from the entry state `σe` (`uV s = uV σe`,
  sb1's `BR σe s`); the entry's `P3 N`, `ScKind`, `IdleScOutV`, `VfhAll` are read
  through the frame. `js_auto`: the nine families (sl1, il1, sb1, sl2's NB, nq1,
  the current thread, ut7's node, the idle SC, ut1's view).
* **`sl_fl4HandleInvocationR`**: post `SLN I [] ∧ (fp → SL I [ct])`; the decode's
  facts (ut7 `InvOKN` / `DecodedFrom`, il2 `NoDelI`, `InvNF`, vi3 `TgOK`,
  `NBind`, and `TcbFh` from sb2's `BindOK` with the entry's `VfhAll`).
-/
import Fl4Proofs.P3.SpecInvSlP3
import Fl4Proofs.P3.SpecInvNtfnQLS
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## The notification-bind fact at the decode's end -/

theorem keep_decBind (scPtr : ObjRef) (ex : List Cap) (σ : State Unit) :
    IKE (fun t => t = σ) (decodeSchedContextBind (Z := Unit) scPtr ex) := by
  unfold decodeSchedContextBind
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDetE.whenE))

/-- Not a notification bind. -/
def NBnd : SchedContextInvocation → Prop
  | .invokeSchedContextBind _ (.notificationCap _ _ _) => False
  | _ => True

theorem nbindS_of {s : State Unit} {a : SchedContextInvocation} (h : NBnd a) : NBindS s a := by
  cases a with
  | invokeSchedContextBind c cap =>
    cases cap with
    | notificationCap n b r => exact absurd h id
    | _ => trivial
  | _ => trivial

theorem decS_scBind (scPtr : ObjRef) (ex : List Cap) (σ : State Unit) :
    ∀ a s, ((.ok a, s) : Except SyscallError SchedContextInvocation × State Unit) ∈
      ((decodeSchedContextBind (Z := Unit) scPtr ex).run σ).1 → NBindS s a := by
  intro a s h
  have e : s = σ := keep_decBind scPtr ex σ σ rfl _ h
  subst e
  exact dec_bindNtfn scPtr ex s a s h

theorem decS_sc (label : Data) (scPtr : ObjRef) (ex : List Cap) (σ : State Unit) :
    ∀ a s, ((.ok a, s) : Except SyscallError SchedContextInvocation × State Unit) ∈
      ((decodeSchedContextInvocation (Z := Unit) label scPtr ex).run σ).1 → NBindS s a := by
  unfold decodeSchedContextInvocation
  split
  · intro a s h
    have e := mem_ret_ok h
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    rw [e.1]; trivial
  · exact decS_scBind scPtr ex σ
  all_goals refine fun a s h => nbindS_of ((?_ : SInvB.OkA NBnd _) σ a s h)
  all_goals first
    | exact SInvB.okA_throw _
    | (unfold decodeSchedContextUnbindObject; okA_auto)
    | (unfold decodeSchedContextYieldTo; okA_auto)
    | okA_auto

/-- Not an SC invocation. -/
def NScI : Fl4Invocation → Prop
  | .invokeSchedContext _ => False
  | _ => True

theorem nbind_of {s : State Unit} {a : Fl4Invocation} (h : NScI a) : NBind s a := by
  cases a with
  | invokeSchedContext i => exact absurd h id
  | _ => trivial

/-- **The decode's notification-bind fact at its end state.** -/
theorem decS_nBind (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    ∀ a s, ((.ok a, s) : Except SyscallError Fl4Invocation × State Unit) ∈
      ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ).1 → NBind s a := by
  cases cap with
  | schedContextCap sc sz =>
    intro a s h
    simp only [fl4DecodeInvocation] at h
    split at h
    · exact absurd (congrArg Prod.fst (Set.mem_singleton_iff.1 h)) (by simp)
    · unfold NonDetE.liftME at h
      obtain ⟨z, hz, ⟨a', ha', hy⟩ | ⟨e, -, he⟩⟩ := mem_bindE' h
      · obtain ⟨r, s'⟩ := z
        simp only at ha'; subst ha'
        have e := Set.mem_singleton_iff.1 hy
        simp only [Prod.mk.injEq, Except.ok.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact decS_sc _ _ _ σ a' _ hz
      · simp at he
  | _ =>
    refine fun a s h => nbind_of ((?_ : SInvB.OkA NScI _) σ a s h)
    unfold fl4DecodeInvocation
    (try dsimp only)
    repeat' (first
      | exact SInvB.okA_throw _ | exact SInvB.okA_returnOk trivial
      | (exact SInvB.okA_liftME (SInvB.okA_triv fun _ => trivial))
      | (refine SInvB.okA_ite ?_ ?_)
      | split)

/-! ## The shell invariant -/

/-- **The shell invariant** (see the module docstring). -/
def Js (I : ObjRef × ObjRef) (ct : ObjRef) (d : Prop) (N : Irq → ObjRef) (σe s : State Unit) : Prop :=
  SAP I [ct] [ct] d ct s ∧ NQ [ct] s ∧ s.curThread = ct ∧ NodeIs N s ∧ IdleScIs I.2 s ∧
    uV s = uV σe ∧ SInvB.BR σe.kheap s.kheap

/-- The entry's facts read through the frame. -/
def EF (N : Irq → ObjRef) (σe : State Unit) : Prop := P3 N σe ∧ ScKind σe ∧ IdleScOutV σe ∧ VfhAll σe

/-- The post of `handle_invocation`. -/
def JS (I : ObjRef × ObjRef) (ct : ObjRef) (fp : Bool) (s : State Unit) : Prop :=
  (SL I [] s ∧ NtfnScB s) ∧ (fp = true → SL I [ct] s)

section J
variable {I : ObjRef × ObjRef} {ct : ObjRef} {d : Prop} {N : Irq → ObjRef} {σe : State Unit}

theorem js_ofK {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I [ct] m) (h2 : ILK [ct] m)
    (h3 : ∀ h0, SInvB.SBK h0 m) (h4 : NBK m) (h5 : NQK [ct] m) (h6 : CTK ct m) (h7 : SInvU.NK N m) (h8 : IsK I.2 m)
    (h9 : ∀ v, UK v m) : IK (Js I ct d N σe) m := fun σ h y hy =>
  ⟨sap_ik h1 h2 h3 h4 σ h.1 y hy, h5 σ h.2.1 y hy, h6 σ h.2.2.1 y hy, h7 σ h.2.2.2.1 y hy,
    h8 σ h.2.2.2.2.1 y hy, (h9 _ σ rfl y hy).trans h.2.2.2.2.2.1,
    SInvB.BR.trans h.2.2.2.2.2.2 (SInvB.br_mem_of_sbk h3 hy)⟩

macro "js_auto" : tactic => `(tactic| exact js_ofK (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)
  (by nq_auto) (by ct_auto) (by nk_auto) (by isk_auto) (fun _ => by uk_auto))

theorem js_post {fp : Bool} {s : State Unit} (h : Js I ct d N σe s) : JS I ct fp s :=
  ⟨⟨sl_mono h.1.1.1 (fun _ h => by cases h), h.1.2.2⟩, fun _ => h.1.1.1⟩

theorem js_sts : IK (Js I ct d N σe) (setThreadState (Z := Unit) ct .restart) :=
  js_ofK (sl_setThreadState _ _) (il_setThreadState ct .restart (fun _ => List.mem_singleton_self _))
    (fun _ => by sb_auto) (by nb_auto) (nq_setThreadState ct .restart (List.mem_singleton_self _) (fun h => h))
    (ct_setThreadState _ _) (by nk_auto) (by isk_auto) (fun _ => uk_setThreadState _ _)

theorem spf_of {s : State Unit} (hJ : Js I ct d N σe s) (hE : EF N σe) (hI : I.2 = σe.idleSc) :
    SPF I [ct] [ct] d ct N s := by
  refine ⟨hJ.1, nq_weak_nil _ hJ.2.1, p3_of_view hJ.2.2.2.2.2.1 hE.1, hJ.2.2.2.1, hJ.2.2.2.2.1, ?_, ?_⟩
  · show ScKindV (uV s); rw [hJ.2.2.2.2.2.1]; exact hE.2.1
  · show IrqOutV (fun _ => s.idleSc) (uV s)
    rw [hJ.2.2.2.2.2.1, show s.idleSc = σe.idleSc from hJ.2.2.2.2.1.trans hI]; exact hE.2.2.1

/-- `set_thread_state` keeps the notification-bind fact. -/
theorem nbind_sts {s : State Unit} {b : Fl4Invocation} (h : NBind s b) {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) ct .restart s).1) : NBind y.2 b := by
  cases b with
  | invokeSchedContext i =>
    cases i with
    | invokeSchedContextBind c cap =>
      cases cap with
      | notificationCap n bb r => exact scn_sts c ct .restart s h y hy
      | _ => trivial
    | _ => trivial
  | _ => trivial

/-- The fault-handler fact of a `threadControlSched` bind from sb2's `BindOK` and the entry's `VfhAll`. -/
theorem tcbFh_of {s : State Unit} (hJ : Js I ct d N σe s) (hE : EF N σe) {b : Fl4Invocation}
    (hB : SInvB.BindOK (SInvB.bv s.kheap) b) : ∀ ti, b = .invokeTCB ti → TcbFh s ti := by
  intro ti e
  subst e
  cases ti with
  | threadControlSched t sl fh mcp prio sc =>
    rcases sc with _ | _ | c
    · trivial
    · trivial
    · obtain ⟨x, hx, -⟩ := SInvB.bv_t.1 hB.2
      obtain ⟨x0, hx0⟩ := hJ.2.2.2.2.2.2.tcb' t x hx
      intro c0 hc0
      have hv : SInvU.capAt s = SInvU.capAt σe := congrArg (fun w : UView => w.2.1) hJ.2.2.2.2.2.1
      rw [hv, SInvB.capAt_fh hx0] at hc0
      cases hc0
      exact SInvB.fhC_of_valid (hE.2.2.2 t x0 hx0)
  | _ => trivial

end J

/-! ## `handle_invocation` -/

set_option maxHeartbeats 16000000 in
theorem sl_fl4HandleInvocationR (hG : SlGap) (I : ObjRef × ObjRef) (N : Irq → ObjRef) (σe : State Unit)
    (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σe)) (ct : ObjRef) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    HKE (Js I ct (don = true ∧ calling = false) N σe) (JS I ct fp)
      (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.2.2.1
  simp only [hc, withoutPreemption]
  refine hke_bind (R := Js I ct (don = true ∧ calling = false) N σe) (hk_liftE (hk_of_ik ?_)) (fun info => ?_)
    (fun s h => js_post h) σ hσ
  · js_auto
  intro σ' hσ' y0 hy0
  have hF : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) ct cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false ct
       let extracaps ← lookupExtraCaps ct buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hOk : OkV (uV σ') (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV σ').2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV σ').2.1 p.2 = some p.1 ∧ DestRefV (uV σ') p.2) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) ct cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false ct
       let extracaps ← lookupExtraCaps ct buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCapsN _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine ft_syscall_post (I := Js I ct (don = true ∧ calling = false) N σe) (Q := JS I ct fp) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · refine (?_ : IKE (Js I ct (don = true ∧ calling = false) N σe) _) σ' hσ'
    js_auto
  · intro f s hs v hv
    unfold NonDet.when at hv
    split at hv
    · have h1 := sl_handleFault (I := I) (K := [ct]) (L := [ct]) (d := don = true ∧ calling = false) (t := ct)
        ct f s hs.1 v hv
      exact ⟨⟨sl_mono h1 (fun _ h => by cases h), nb_handleFault ct f s hs.1.2.2 v hv⟩, fun _ => h1⟩
    · rw [Set.mem_singleton_iff.1 hv]; exact js_post hs
  · intro a s has w hw
    have hs : Js I ct (don = true ∧ calling = false) N σe s := by
      refine (?_ : IKE (Js I ct (don = true ∧ calling = false) N σe) _) σ' hσ' _ has
      js_auto
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (Js I ct (don = true ∧ calling = false) N σe) _) s hs w hw
    js_auto
  · intro e s hs v hv
    have h1 : SL I [ct] v.2 := by
      refine (?_ : SLK I [ct] _) s hs.1.1.1 v hv
      sl_auto
    have h2 : NtfnScB v.2 := by
      refine (?_ : NBK _) s hs.1.2.2 v hv
      nb_auto
    exact ⟨⟨sl_mono h1 (fun _ h => by cases h), h2⟩, fun _ => h1⟩
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ' := hF _ σ' rfl _ has
    obtain ⟨hcap, hex⟩ := hOk σ' rfl _ s has
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hvx : uV x0.2 = uV σ' := (uk_getMrs (uvw := uV s) _ _ _ s rfl x0 hx0).trans hvs
    have hdec : InvOKN (uV σ') b :=
      okv_fl4DecodeN fp info.miLabel x0.1 cptr sl cap ex buf hcap hex x0.2 hvx b s' hb0
    have hDF : DecodedFrom (uV σ') b :=
      ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hvx, hcap, hex, hb0⟩
    have hnf : InvNF (uV σ') b := okv_invNF fp info.miLabel x0.1 cptr sl cap ex buf x0.2 hvx b s' hb0
    have hfp : fp = true → NoDelI b := okv_fpI fp info.miLabel x0.1 cptr sl cap ex buf x0.2 hvx b s' hb0
    have hNB : NBind s' b := decS_nBind fp info.miLabel x0.1 cptr sl cap ex buf x0.2 b s' hb0
    have hJx : Js I ct (don = true ∧ calling = false) N σe x0.2 := by
      refine (?_ : IK (Js I ct (don = true ∧ calling = false) N σe) _) s ?_ x0 hx0
      · js_auto
      · refine (?_ : IKE (Js I ct (don = true ∧ calling = false) N σe) _) σ' hσ' _ has
        js_auto
    have hBO : SInvB.BindOK (SInvB.bv x0.2.kheap) b :=
      SInvB.okb_fl4Decode (SInvB.bv x0.2.kheap) fp info.miLabel x0.1 cptr sl cap ex buf x0.2 rfl b s' hb0
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      have hJ1 : Js I ct (don = true ∧ calling = false) N σe w.2 := js_sts s' hI w hw
      have hNB1 : NBind w.2 b := nbind_sts hNB hw
      obtain ⟨r, s1⟩ := w
      dsimp only at hJ1 hNB1
      have hv1 : uV s1 = uV σ' := hJ1.2.2.2.2.2.1.trans hσ'.2.2.2.2.2.1.symm
      have hok1 : InvOKN (uV s1) b := by rw [hv1]; exact hdec
      have hnf1 : InvNF (uV s1) b := by rw [hv1]; exact hnf
      have hDF1 : DecodedFrom (uV s1) b := by rw [hv1]; exact hDF
      have hT1 : SInvI.TgOK (uV s1) b := SInvI.tgOK_of hDF1
      have hB1 : SInvB.BindOK (SInvB.bv s1.kheap) b := by
        have e1 : SInvB.bv s1.kheap = SInvB.bv x0.2.kheap :=
          (SInvB.bv_of_br hJ1.2.2.2.2.2.2).trans (SInvB.bv_of_br hJx.2.2.2.2.2.2).symm
        rw [e1]; exact hBO
      have hc1 : s1.curThread = ct := hJ1.2.2.1
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := sl_fl4PerformInvocation hG I N blocking calling don fp b s1 [ct] [ct]
          (by rw [hc1]; exact spf_of hJ1 hE hI2) (by rw [hJ1.2.2.2.2.2.1]; exact hI1) hfp hok1 hnf1 hT1 hNB1 (tcbFh_of hJ1 hE hB1) hDF1 _ hz2
        refine ⟨⟨(?_ : SLKE I [] _) s2 hs2.1.1 y hy, (?_ : NBKE _) s2 hs2.1.2 y hy⟩,
          fun hf => (?_ : SLKE I [ct] _) s2 (hs2.2 hf) y hy⟩
        · sl_auto
        · nb_auto
        · sl_auto
      · exact sl_fl4PerformInvocation hG I N blocking calling don fp b s1 [ct] [ct]
          (by rw [hc1]; exact spf_of hJ1 hE hI2) (by rw [hJ1.2.2.2.2.2.1]; exact hI1) hfp hok1 hnf1 hT1 hNB1 (tcbFh_of hJ1 hE hB1) hDF1 _ hz2
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      exact js_post (js_sts s' hI w hw)

end

end Fl4Proofs.P3.SInvL
