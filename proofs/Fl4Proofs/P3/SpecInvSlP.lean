/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive across the CNode, IRQ
handler and SC performs; NtfnScB across the SC-notification bind** (sl2
handoff 3, first part; spec side only).

* CNode moves / rotations: the moved cap names what the read cap named (`NF`):
  the decode builds it by `mask_cap` / `update_cap_data`, which keep thread and
  SC caps (`okv_cnNF`, `okv_invNF`: the CNode dispatch only; ut5's `RefEq` does
  not separate an SC cap from an endpoint cap to the same address). `sl_capMove`,
  `sl_capSwapR`, **`sl_invokeCnode`** (delete / revoke by `sdu_*`).
* `sl_invokeIrqHandler` (`cap_delete_one` with IfLiveT, `cap_insert`).
* `sl_invokeSchedContext`: the bound SC and TCB are held (vi3's `ScTg`), so named.
* **`nb_bindNtfn`**: `sched_context_bind_ntfn c n` keeps NtfnScB when `c` has no
  notification (then no notification points to `c`); the decode checks it at its
  state (`dec_bindNtfn`: the SC decode reads only), and `set_thread_state` keeps
  SCs (`scn_sts`).
-/
import Fl4Proofs.P3.SpecInvSlD3
import Fl4Proofs.P3.SpecInvViK
import Fl4Proofs.P3.SpecInvNtfnQLP
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## The names a moved cap keeps -/

/-- `c` names every object `c0` names (thread / SC caps). -/
def NF (c0 c : Cap) : Prop := ∀ p, NCap p c0 → NCap p c

theorem nf_mask (R : CapRights) (c : Cap) : NF c (maskCap R c) := by
  intro p h; cases c <;> simp_all [NCap, maskCap, capRightsUpdate]

theorem nf_upd (b : Bool) (x : Data) (c : Cap) : NF c (updateCapData b x c) := by
  intro p h
  cases c <;> simp_all [NCap, updateCapData, isEpCap, isNtfnCap, isCnodeCap, isArchCap]

theorem nf_trans {a b c : Cap} (h1 : NF a b) (h2 : NF b c) : NF a c := fun p h => h2 p (h1 p h)

/-- The CNode decode's moved caps. -/
def CnNF (w : UView) : CnodeInvocation → Prop
  | .moveCall c src _ => ∀ c0, w.2.1 src = some c0 → NF c0 c
  | .rotateCall c1 c2 s1 s2 _ => (∀ c0, w.2.1 s1 = some c0 → NF c0 c1) ∧ (∀ c0, w.2.1 s2 = some c0 → NF c0 c2)
  | _ => True

set_option maxHeartbeats 4000000 in
theorem okv_cnNF {w : UView} (label : Data) (args : List Data) (cap : Cap) (ex : List Cap) :
    OkV w (CnNF w) (decodeCnodeInvocation (Z := Unit) label args cap ex) := by
  unfold decodeCnodeInvocation
  refine okv_unlessE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk_bind (okv_returnOk_bind
    (okv_returnOk_bind (okv_bind_uk (fun _ => uk_lookupTargetSlot _ _ _) fun destSlot => ?_)))
  refine okv_ite ?_ (okv_ite (okv_returnOk trivial) (okv_ite (okv_returnOk trivial) (okv_ite ?_ (okv_ite ?_ (okv_throw _)))))
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))
    refine okv_bind_uk (fun _ => uk_ensureEmpty _) fun _ => ?_
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_liftE_getCap_bind fun srcCap hsc => okv_whenE_bind fun hnn => ?_
    refine okv_bind_uk (fun _ => by uk_auto) fun x => ?_
    obtain ⟨rights, capData, isMove⟩ := x
    dsimp only
    refine okv_returnOk_bind ?_
    cases isMove
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact okv_bind_uk (fun _ => uk_deriveCap _ _) fun nc => okv_whenE_bind fun _ => okv_returnOk trivial
    · simp only [↓reduceIte]
      refine okv_returnOk_bind (okv_whenE_bind fun _ => okv_returnOk ?_)
      intro c0 hc0
      rw [hsc] at hc0; cases hc0
      cases capData with
      | none => exact nf_mask _ _
      | some x => exact nf_trans (nf_mask rights _) (nf_upd _ _ _)
  · repeat' okv_step
    all_goals exact okv_returnOk trivial
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind
      (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))))))
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_bind_uk (fun _ => uk_lookupPivotSlot _ _ _) fun pivotSlot => ?_
    refine okv_whenE_bind fun _ => ?_
    refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_
    refine okv_liftE_getCap_bind fun srcCap hsc => okv_whenE_bind fun _ => ?_
    refine okv_liftE_getCap_bind fun pivCap hpc => okv_whenE_bind fun _ => ?_
    refine okv_returnOk_bind (okv_returnOk_bind (okv_whenE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk ?_))
    refine ⟨fun c0 h => ?_, fun c0 h => ?_⟩
    · rw [hsc] at h; cases h; exact nf_upd _ _ _
    · rw [hpc] at h; cases h; exact nf_upd _ _ _

/-- The CNode dispatch's moved caps. -/
def InvNF (w : UView) : Fl4Invocation → Prop
  | .invokeCNode ci => CnNF w ci
  | _ => True

theorem okv_invNF {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkV w (InvNF w) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | cnodeCap r b g =>
    unfold fl4DecodeInvocation
    exact okv_ite (okv_throw _) (okv_liftME (okv_cnNF _ _ _ _))
  | _ =>
    unfold fl4DecodeInvocation
    (try dsimp only)
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | split)

/-! ## Moves -/

theorem nl_capMove (σ0 : State Unit) (c : Cap) (src dest : CslotPtr) :
    IK (NLs σ0) (capMove (Z := Unit) c src dest) := by
  unfold capMove
  repeat' (first
    | (with_reducible exact nl_setCap _ _ _)
    | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)
    | ik_step0 | ik_unfold)

section M
variable {I : ObjRef × ObjRef} {K : List ObjRef}

theorem sl_of_caps {σ σ' : State Unit} (hσ : SL I K σ) (hs : NLs σ σ') (hT : ∀ t, HasN σ t → HasN σ' t) :
    SL I K σ' := by
  refine ⟨fun t o ht hl h1 h2 => ?_, fun t ht => (hσ.2 t ht).imp_left (hT t)⟩
  obtain ⟨o0, ho0, hl0⟩ := hs t o ht hl
  exact hT t (hσ.1 t o0 ho0 hl0 h1 h2)

/-- **`cap_move`** of a cap naming what the source cap named, into a null slot. -/
theorem sl_capMove (c0 c : Cap) (src dest : CslotPtr) (σ : State Unit) (hs : SInvU.capAt σ src = some c0)
    (hd : SInvU.capAt σ dest = some .nullCap) (hr : NF c0 c) :
    IKp (SL I K) σ (capMove (Z := Unit) c src dest) := by
  intro hσ y hy
  have hcap := capMove_caps hy
  refine sl_of_caps hσ (nl_capMove σ c src dest σ (fun p o hp hl => ⟨o, hp, hl⟩) y hy) ?_
  rintro t ⟨x, c', hx, hn⟩
  by_cases e1 : x = src
  · subst e1
    rw [hs] at hx; cases hx
    have hne : dest ≠ x := fun e => by rw [e, hs] at hd; cases hd; exact hn
    exact ⟨dest, c, by rw [hcap, if_neg hne, if_pos rfl], hr t hn⟩
  · by_cases e2 : x = dest
    · subst e2; rw [hd] at hx; cases hx; exact absurd hn id
    · exact ⟨x, c', by rw [hcap, if_neg e1, if_neg e2]; exact hx, hn⟩

/-- **`cap_swap`** of caps naming what the read caps named. -/
theorem sl_capSwapR (c1 c2 c1' c2' : Cap) (s1 s2 : CslotPtr) (σ : State Unit) (hne : s1 ≠ s2)
    (h1 : SInvU.capAt σ s1 = some c1') (h2 : SInvU.capAt σ s2 = some c2') (r1 : NF c1' c1) (r2 : NF c2' c2) :
    IKp (SL I K) σ (capSwap (Z := Unit) c1 s1 c2 s2) := by
  intro hσ y hy
  have hcap := capSwap_capAt hne hy
  refine sl_of_caps hσ (nl_capSwap σ c1 c2 s1 s2 σ (fun p o hp hl => ⟨o, hp, hl⟩) y hy) ?_
  rintro t ⟨x, c', hx, hn⟩
  by_cases e1 : x = s1
  · subst e1
    rw [h1] at hx; cases hx
    exact ⟨s2, c1, by rw [hcap, if_pos rfl], r1 t hn⟩
  · by_cases e2 : x = s2
    · subst e2
      rw [h2] at hx; cases hx
      exact ⟨s1, c2, by rw [hcap, if_neg hne, if_pos rfl], r2 t hn⟩
    · exact ⟨x, c', by rw [hcap, if_neg e2, if_neg e1]; exact hx, hn⟩

end M

/-! ## `invoke_cnode` -/

theorem sl_invokeCnode (I : ObjRef × ObjRef) (i : CnodeInvocation) (σ : State Unit) (hσ : SDU I σ)
    (hok : CnOKN (uV σ) i) (hnf : CnNF (uV σ) i) :
    ∀ y ∈ ((invokeCnode (Z := Unit) i).run σ).1, SL I [] y.2 := by
  have hS : SL I [] σ := hσ.2.1
  cases i
  case revokeCall s => exact fun y hy => (sdu_capRevoke s σ hσ y hy).2.1
  case deleteCall s => exact fun y hy => (sdu_capDelete s σ hσ y hy).2.1
  case insertCall c src dest =>
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact sl_capInsert c src dest σ hS x hx
  case moveCall c src dest =>
    obtain ⟨c0, hs, hd, -, -, -, -⟩ := hok
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact sl_capMove c0 c src dest σ hs hd (hnf c0 hs) hS x hx
  case rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, -, -, -, -, h21, h23, -, h3⟩ := hok
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    split at hx
    · exact sl_capSwapR c1 c2 c1' c2' s1 s2 σ (Ne.symm h21) h1 h2 (hnf.1 c1' h1) (hnf.2 c2' h2) hS x hx
    · rename_i e13
      obtain ⟨x1, hx1, hx⟩ := hx
      have hcaps := capMove_caps hx1
      have hL1 : SL I [] x1.2 := sl_capMove c2' c2 s2 s3 σ h2 (h3 e13) (hnf.2 c2' h2) hS x1 hx1
      have h1' : SInvU.capAt x1.2 s1 = some c1' := by
        rw [hcaps, if_neg (Ne.symm h21), if_neg e13]; exact h1
      have h2' : SInvU.capAt x1.2 s2 = some .nullCap := by rw [hcaps, if_pos rfl]
      exact sl_capMove c1' c1 s1 s2 x1.2 h1' h2' (hnf.1 c1' h1) hL1 x hx
  case cancelBadgedSendsCall c =>
    intro y hy
    cases c
    case endpointCap ep b g =>
      simp only [invokeCnode, withoutPreemption] at hy
      exact (ike_liftE (ik_when _ (sl_cancelBadgedSends ep b)) σ hS y hy)
    all_goals
      simp only [invokeCnode] at hy
      exact (ike_liftE ik_fail) σ hS y hy

/-! ## `invoke_irq_handler` -/

section H
variable {I : ObjRef × ObjRef} {K : List ObjRef}

theorem sl_invokeIrqHandler (i : IrqHandlerInvocation) : HK (SLI0 I K) (SL I K) (invokeIrqHandler (Z := Unit) i) := by
  cases i <;> simp only [invokeIrqHandler]
  case aCKIrq irq => exact shk_ik (sl_archInvokeIrqHandler _) fun _ h => h.1
  case setIRQHandler irq cap slot =>
    unfold getIrqSlot
    intro σ h x ⟨y, hy, hx⟩
    rw [Set.mem_singleton_iff.1 hy] at hx
    exact (shk_bind (sl_capDeleteOne _) fun _ => shk_ik (sl_capInsert _ _ _) fun _ h => h) σ h x hx
  case clearIRQHandler irq =>
    unfold getIrqSlot
    intro σ h x ⟨y, hy, hx⟩
    rw [Set.mem_singleton_iff.1 hy] at hx
    exact sl_capDeleteOne _ σ h x hx

/-! ## `invoke_sched_context` -/

theorem hasN_of_held {σ : State Unit} {c : Cap} (h : SInvI.Held (uV σ) c) {p : ObjRef} (hp : NCap p c) :
    HasN σ p := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, c, hs, hp⟩

theorem sl_invokeSchedContext (iv : SchedContextInvocation) (σ : State Unit) (hT : SInvI.ScTg (uV σ) iv) :
    IKp (SL I K) σ (invokeSchedContext (Z := Unit) iv) := by
  cases iv
  case invokeSchedContextBind p cap =>
    obtain ⟨⟨sz, hp⟩, hc⟩ := hT
    simp only [invokeSchedContext]
    cases cap
    case threadCap t =>
      intro hσ y hy
      have h1 : SL I (p :: t :: K) σ := sl_cons (sl_cons hσ (Or.inl (hasN_of_held hc rfl)))
        (Or.inl (hasN_of_held hp rfl))
      refine sl_tail (sl_tail ((?_ : SLK I (p :: t :: K) _) σ h1 y hy))
      exact ik_bind (sl_schedContextBindTcb p t (List.mem_cons_self) (List.mem_cons_of_mem _ List.mem_cons_self))
        fun _ => ik_pure _
    case notificationCap n b r =>
      intro hσ y hy
      have h1 : SL I (p :: K) σ := sl_cons hσ (Or.inl (hasN_of_held hp rfl))
      refine sl_tail ((?_ : SLK I (p :: K) _) σ h1 y hy)
      exact ik_bind (sl_schedContextBindNtfn p n List.mem_cons_self) fun _ => ik_pure _
    all_goals exact ikp_of_ik ik_fail σ
  all_goals exact ikp_of_ik (by simp only [invokeSchedContext]; sl_auto) σ

end H

/-! ## The SC-notification bind keeps NtfnScB -/

/-- SC `c` has no notification. -/
def ScNoN (c : ObjRef) (σ : State Unit) : Prop := ∀ y k, σ.kheap c = some (.schedContext y k) → y.scNtfn = none

theorem nb_bindNtfn (c n : ObjRef) (σ : State Unit) (hσ : NtfnScB σ) (hc : ScNoN c σ) :
    ∀ x ∈ (schedContextBindNtfn (Z := Unit) c n σ).1, NtfnScB x.2 := by
  intro x hx
  unfold schedContextBindNtfn at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  unfold setNtfnObjRef updateSkObjRef at hy1
  obtain ⟨⟨a, s⟩, hz, hy1⟩ := hy1
  obtain ⟨hk, ez⟩ := mem_getSimpleKo hz
  simp only at hk ez; subst s
  obtain ⟨o0, ho0, -, -, e1⟩ := mem_setSimpleKoN hy1
  obtain ⟨yc, k, hkc, e2⟩ := SInvB.mem_updateSchedContext hx
  have hk1 : y1.2.kheap = Function.update σ.kheap n
      (some (.notification (ntfnScUpdate (fun _ => some c) a))) := by rw [e1]
  rw [hk1] at hkc
  have hcn : c ≠ n := by intro e; subst e; rw [Function.update_self] at hkc; cases hkc
  rw [Function.update_of_ne hcn] at hkc
  have hK : x.2.kheap = Function.update (Function.update σ.kheap n
      (some (.notification (ntfnScUpdate (fun _ => some c) a)))) c
      (some (.schedContext (scNtfnUpdate (fun _ => some n) yc) k)) := by rw [e2]; dsimp only; rw [hk1]
  intro n' ntf c' hn' hc'
  rw [hK] at hn'; rw [hK]
  by_cases e3 : n' = c
  · subst e3; rw [Function.update_self] at hn'; cases hn'
  rw [Function.update_of_ne e3] at hn'
  by_cases e4 : n' = n
  · subst e4
    rw [Function.update_self] at hn'
    simp only [Option.some.injEq, KernelObject.notification.injEq] at hn'
    subst hn'
    simp only [ntfnScUpdate, Option.some.injEq] at hc'
    subst hc'
    exact ⟨_, k, Function.update_self _ _ _, rfl⟩
  · rw [Function.update_of_ne e4] at hn'
    obtain ⟨y0, k0, hy0, hyn⟩ := hσ n' ntf c' hn' hc'
    by_cases e5 : c' = c
    · subst e5
      rw [hkc] at hy0; cases hy0
      rw [hc yc k hkc] at hyn; cases hyn
    · have e6 : c' ≠ n := by intro e; subst e; rw [hk] at hy0; cases hy0
      exact ⟨y0, k0, by rw [Function.update_of_ne e5, Function.update_of_ne e6]; exact hy0, hyn⟩

/-- `set_thread_state` writes a TCB only. -/
theorem scn_sts (c : ObjRef) (t : ObjRef) (ts : ThreadState) : IK (ScNoN c) (setThreadState (Z := Unit) t ts) := by
  intro σ hσ y hy
  unfold setThreadState at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨x, hx, e⟩ := SInvB.mem_threadSet hy1
  have hk := kh_setThreadStateAct t y1.2.kheap y1.2 rfl y hy
  intro yc k hyc
  rw [hk, e] at hyc
  have hne : c ≠ t := by intro e'; subst e'; simp at hyc
  simp only [Function.update_of_ne hne] at hyc
  exact hσ yc k hyc

/-! ## Decode outcomes read at a fixed state -/

/-- Every `.ok` outcome of `m` from `σ0` satisfies `P`. -/
def OkR (σ0 : State Unit) {ε α : Type} (P : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ0).1 → P a

section R
variable {σ0 : State Unit} {ε α β : Type}

theorem okR_returnOk {P : α → Prop} {a : α} (h : P a) : OkR σ0 P (NonDetE.returnOk a : NonDetE (State Unit) ε α) := by
  intro a' s hs
  have e := mem_ret_ok hs
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  rw [e.1]; exact h

theorem okR_throw_bind {P : β → Prop} (e : ε) {g : α → NonDetE (State Unit) ε β} :
    OkR σ0 P (NonDetE.throwError e >>= g) := by
  intro a s h
  obtain ⟨z, hz, ⟨b, hb, -⟩ | ⟨er, -, he⟩⟩ := mem_bindE' h
  · rw [Set.mem_singleton_iff.1 hz] at hb; simp at hb
  · simp at he

theorem okR_throw {P : α → Prop} (e : ε) : OkR σ0 P (NonDetE.throwError e : NonDetE (State Unit) ε α) := by
  intro a s h
  exact absurd (congrArg Prod.fst (Set.mem_singleton_iff.1 h)) (by simp)

theorem okR_ite {P : α → Prop} {c : Prop} [Decidable c] {m1 m2 : NonDetE (State Unit) ε α} (h1 : OkR σ0 P m1)
    (h2 : OkR σ0 P m2) : OkR σ0 P (if c then m1 else m2) := by
  split <;> assumption

theorem okR_liftME {P : β → Prop} {f : α → β} {m : NonDetE (State Unit) ε α} (h : OkR σ0 (fun a => P (f a)) m) :
    OkR σ0 P (NonDetE.liftME f m) := by
  unfold NonDetE.liftME
  intro b s hb
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hb
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    have e := Set.mem_singleton_iff.1 hy
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h _ _ hz
  · simp at he

/-- A step keeping the state, its value satisfying `Q`. -/
theorem okR_bindQ {P : β → Prop} {Q : α → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ z ∈ (m.run σ0).1, ∀ a, z.1 = .ok a → z.2 = σ0 ∧ Q a) (hg : ∀ a, Q a → OkR σ0 P (g a)) :
    OkR σ0 P (m >>= g) := by
  intro b s h
  obtain ⟨z, hz, ⟨a, ha, h⟩ | ⟨e, -, he⟩⟩ := mem_bindE' h
  · obtain ⟨e1, hq⟩ := hm z hz a ha
    rw [e1] at h
    exact hg a hq b s h
  · simp at he

theorem okR_bind_k {P : β → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKE (fun t => t = σ0) m) (hg : ∀ a, OkR σ0 P (g a)) : OkR σ0 P (m >>= g) :=
  okR_bindQ (Q := fun _ => True) (fun z hz _ _ => ⟨hm σ0 rfl z hz, trivial⟩) fun a _ => hg a

theorem okR_returnOk_bind {P : β → Prop} {a : α} {g : α → NonDetE (State Unit) ε β} (h : OkR σ0 P (g a)) :
    OkR σ0 P (NonDetE.returnOk a >>= g) :=
  okR_bindQ (Q := fun x => x = a) (fun z hz x hx => by
    rw [mem_ret_ok hz] at hx ⊢; cases hx; exact ⟨rfl, rfl⟩) fun x hx => hx ▸ h

theorem okR_whenE_bind {P : β → Prop} {c : Prop} [Decidable c] {e : ε} {g : Unit → NonDetE (State Unit) ε β}
    (h : ¬ c → OkR σ0 P (g ())) : OkR σ0 P (NonDetE.whenE c (NonDetE.throwError e) >>= g) := by
  unfold NonDetE.whenE
  by_cases hc : c
  · rw [if_pos hc]; exact okR_throw_bind e
  · rw [if_neg hc]
    refine okR_bindQ (Q := fun _ => True) (fun z hz _ _ => ⟨?_, trivial⟩) fun u _ => h hc
    rw [Set.mem_singleton_iff.1 hz]

theorem okR_of_okA {P : α → Prop} {m : NonDetE (State Unit) ε α} (h : SInvB.OkA P m) : OkR σ0 P m :=
  fun a s hs => h σ0 a s hs

end R

/-- The SC-notification bind's fact. -/
def NBindS (σ : State Unit) : SchedContextInvocation → Prop
  | .invokeSchedContextBind c (.notificationCap _ _ _) => ScNoN c σ
  | _ => True

def NBind (σ : State Unit) : Fl4Invocation → Prop
  | .invokeSchedContext i => NBindS σ i
  | _ => True

theorem ike_keep_getSc (p : ObjRef) (σ0 : State Unit) {ε : Type} :
    ∀ z ∈ ((NonDetE.liftE (ε := ε) (getSchedContext (Z := Unit) p)).run σ0).1, ∀ a, z.1 = .ok a →
      z.2 = σ0 ∧ ∃ k, σ0.kheap p = some (.schedContext a k) := by
  intro z hz a ha
  obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
  simp only [Except.ok.injEq] at ha
  subst ha
  obtain ⟨e, k, hk⟩ := SInvB.mem_getSchedContext' hx
  exact ⟨e, k, hk⟩

macro "okr_keep" : tactic => `(tactic| (refine okR_bind_k (by repeat' (first | ik_step0 | ik_unfold | (unfold NonDetE.whenE))) fun _ => ?_))

/-- **The SC decode's notification bind**: the SC had no notification at the decode's state. -/
theorem dec_bindNtfn (scPtr : ObjRef) (ex : List Cap) (σ : State Unit) :
    OkR σ (NBindS σ) (decodeSchedContextBind (Z := Unit) scPtr ex) := by
  unfold decodeSchedContextBind
  refine okR_whenE_bind fun _ => okR_returnOk_bind ?_
  refine okR_bindQ (ike_keep_getSc scPtr σ) fun sc ⟨k, hsc⟩ => ?_
  (try dsimp only)
  split
  · rename_i t heq
    okr_keep; okr_keep; okr_keep; okr_keep; okr_keep
    refine okR_whenE_bind fun _ => okR_returnOk (by rw [heq]; trivial)
  · rename_i n b r heq
    refine okR_whenE_bind fun hn => ?_
    okr_keep
    refine okR_whenE_bind fun _ => okR_returnOk ?_
    rw [heq]
    intro y k' hy
    rw [hsc] at hy; cases hy
    exact not_not.1 hn
  · exact okR_throw_bind _

theorem dec_scNBind (label : Data) (scPtr : ObjRef) (ex : List Cap) (σ : State Unit) :
    OkR σ (NBindS σ) (decodeSchedContextInvocation (Z := Unit) label scPtr ex) := by
  unfold decodeSchedContextInvocation
  split
  · exact okR_returnOk trivial
  · exact dec_bindNtfn scPtr ex σ
  all_goals refine okR_of_okA ?_
  all_goals first
    | exact SInvB.okA_throw _
    | (unfold decodeSchedContextUnbindObject; okA_auto)
    | (unfold decodeSchedContextYieldTo; okA_auto)
    | okA_auto

/-- **The decode's notification-bind fact** (the SC dispatch only). -/
theorem dec_nBind (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkR σ (NBind σ) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | schedContextCap sc sz =>
    unfold fl4DecodeInvocation
    exact okR_ite (okR_throw _) (okR_liftME (dec_scNBind _ _ _ σ))
  | _ =>
    unfold fl4DecodeInvocation
    refine okR_of_okA ?_
    (try dsimp only)
    repeat' (first
      | exact SInvB.okA_throw _ | exact SInvB.okA_returnOk trivial
      | (exact SInvB.okA_liftME (SInvB.okA_triv fun _ => trivial))
      | (refine SInvB.okA_ite ?_ ?_)
      | split)

end

end Fl4Proofs.P3.SInvL
