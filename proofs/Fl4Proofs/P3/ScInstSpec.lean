/-
P3 (DESIGN.md §9), scheduling contexts: **what the spec's fault-handler
install keeps** of the scheduler.

* `SK`: the scheduler-side frame of a cap operation (`VK`, with the ready
  queues, the endpoints, the notifications and the scheduler action kept);
  `PSK m`: every outcome of `m` is `SK`; combinators, `psk_setCap`,
  `psk_capInsert`, `psk_checkCapAt`.
* `emptySlot_tcb`: the spec's `empty_slot` of a TCB slot holding a cap,
  one outcome, `SK`.
* `install_sk`: an Ok outcome of `install_tcb_cap` of the fault-handler
  slot whose old cap is null or a non-final endpoint cap (`capDelete_triv`)
  is `SK`.
* `SK.blkQ`, `SK.bindOK`: `BlkQ` and `BindOK` across `SK`.
-/
import Fl4Proofs.P3.ScInstFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

section Spec
open Fl4Spec

/-- **The scheduler-side frame of a cap operation.** -/
structure SK (σ σ' : State Unit) : Prop where
  vk : VK σ σ'
  rdq : σ'.readyQueues = σ.readyQueues
  ep : ∀ e ep, σ.kheap e = some (.endpoint ep) → σ'.kheap e = some (.endpoint ep)
  ntfn : ∀ n x, σ.kheap n = some (.notification x) → σ'.kheap n = some (.notification x)
  act : σ'.schedulerAction = σ.schedulerAction

theorem SK.refl (σ : State Unit) : SK σ σ :=
  ⟨VK.refl σ, rfl, fun _ _ h => h, fun _ _ h => h, rfl⟩

theorem SK.trans {σ1 σ2 σ3 : State Unit} (h1 : SK σ1 σ2) (h2 : SK σ2 σ3) : SK σ1 σ3 :=
  ⟨h1.vk.trans h2.vk, h2.rdq.trans h1.rdq, fun e ep h => h2.ep e ep (h1.ep e ep h),
    fun n x h => h2.ntfn n x (h1.ntfn n x h), h2.act.trans h1.act⟩

/-- A state change outside the heap and the scheduler fields. -/
theorem SK.of_eq {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (hq : σ'.readyQueues = σ.readyQueues)
    (hr : σ'.releaseQueue = σ.releaseQueue) (hc : σ'.curThread = σ.curThread) (ht : σ'.curTime = σ.curTime)
    (ha : σ'.schedulerAction = σ.schedulerAction) : SK σ σ' := by
  refine ⟨⟨fun p x h => ⟨x, by rw [hk]; exact h, rfl, rfl⟩, fun p y h => ⟨y, by rw [← hk]; exact h⟩,
    fun p y n => by rw [hk], hc, ht, hr, Or.inl ha⟩, hq, fun e ep h => by rw [hk]; exact h,
    fun n x h => by rw [hk]; exact h, ha⟩

/-- Replacing a TCB by one with the same state and SC, or a CNode by a CNode. -/
theorem SK.upd {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (hc : (∃ x y, o = .tcb x ∧ o' = .tcb y ∧ y.tcbState = x.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext) ∨
      (∃ a b a' b', o = .cnode a b ∧ o' = .cnode a' b')) :
    SK σ { σ with kheap := Function.update σ.kheap p (some o') } := by
  have hkn : ∀ q, q ≠ p → (Function.update σ.kheap p (some o')) q = σ.kheap q :=
    fun q hq => Function.update_of_ne hq _ _
  refine ⟨⟨fun q x hq => ?_, fun q y hq => ?_, fun q y n => ?_, rfl, rfl, rfl, Or.inl rfl⟩, rfl,
    fun e ep he => ?_, fun n x hn => ?_, rfl⟩
  · by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq
      rcases hc with ⟨x', y, e1, rfl, h1, h2⟩ | ⟨a, b, a', b', e1, -⟩
      · cases e1; exact ⟨y, by simp, h1, h2⟩
      · cases e1
    · exact ⟨x, by simp only [hkn q e]; exact hq, rfl, rfl⟩
  · by_cases e : q = p
    · subst e
      rcases hc with ⟨x, y', rfl, rfl, -, -⟩ | ⟨a, b, a', b', -, rfl⟩
      · exact ⟨x, hk⟩
      · simp at hq
    · exact ⟨y, by simp only [hkn q e] at hq; exact hq⟩
  · by_cases e : q = p
    · subst e
      simp only [Function.update_self, hk]
      rcases hc with ⟨x, y', rfl, rfl, -, -⟩ | ⟨a, b, a', b', rfl, rfl⟩ <;> simp
    · simp only [hkn q e]
  · have : e ≠ p := by
      rintro rfl; rw [hk] at he; cases he
      rcases hc with ⟨x, y, h, -⟩ | ⟨a, b, a', b', h, -⟩ <;> cases h
    simp only [hkn e this]; exact he
  · have : n ≠ p := by
      rintro rfl; rw [hk] at hn; cases hn
      rcases hc with ⟨x, y, h, -⟩ | ⟨a, b, a', b', h, -⟩ <;> cases h
    simp only [hkn n this]; exact hn

/-! ### `PSK` -/

/-- Every outcome is `SK`. -/
def PSK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → SK σ x.2

theorem psk_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : PSK m)
    (hf : ∀ a, PSK (f a)) : PSK (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem psk_bind' {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : PSK m)
    (hf : ∀ a, PSK (f a)) : PSK (NonDet.bind m f) := psk_bind hm hf

theorem psk_pure {α : Type} (a : α) : PSK (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SK.refl σ

theorem psk_pure' {α : Type} (a : α) : PSK (NonDet.pure a : NonDet (State Unit) α) := psk_pure a

theorem psk_gets {α : Type} (f : State Unit → α) : PSK (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SK.refl σ

theorem psk_get : PSK (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SK.refl σ

theorem psk_assert (P : Prop) : PSK (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact SK.refl σ

theorem psk_fail {α : Type} : PSK (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem psk_assertOpt {α : Type} (o : Option α) : PSK (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact psk_fail
  · exact psk_pure' _

theorem psk_getsThe {α : Type} (f : State Unit → Option α) : PSK (NonDet.getsThe f) := by
  intro σ x hx
  exact psk_assertOpt (f σ) σ x hx

theorem psk_selectF {α : Type} (S : Set α × Prop) : PSK (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact SK.refl σ

theorem psk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : PSK m1) (h2 : PSK m2) :
    PSK (if P then m1 else m2) := by
  split <;> assumption

theorem psk_getObject (p : ObjRef) : PSK (getObject (Z := Unit) p) := psk_getsThe _

theorem psk_get_put {f : State Unit → State Unit} (hf : ∀ σ, SK σ (f σ)) :
    PSK (NonDet.get >>= fun s => NonDet.put (f s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hf σ

theorem psk_modify {f : State Unit → State Unit} (hf : ∀ σ, SK σ (f σ)) : PSK (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hf σ

theorem psk_getCap (sl : CslotPtr) : PSK (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine psk_bind (psk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;>
    repeat (first | exact psk_pure _ | exact psk_pure' _ | exact psk_fail | exact psk_assert _ |
      exact psk_assertOpt _ | (refine psk_bind ?_ (fun _ => ?_)))

/-- `set_object` of `o'` over `o`, compatible as in `SK.upd`. -/
theorem psk_setObject_at {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (hc : (∃ x y, o = .tcb x ∧ o' = .tcb y ∧ y.tcbState = x.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext) ∨
      (∃ a b b', o = .cnode a b ∧ o' = .cnode a b')) :
    ∀ x, x ∈ (setObject (Z := Unit) p o' σ).1 → SK σ x.2 := by
  intro x hx
  unfold setObject at hx
  rw [nd_bind_one (Notif.getObject_eq hk)] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hy
  obtain ⟨z, hz, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hz] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact SK.upd hk (hc.imp_right fun ⟨a, b, b', h1, h2⟩ => ⟨a, b, a, b', h1, h2⟩)

theorem psk_setCap (cap : Cap) (sl : CslotPtr) : PSK (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  intro σ x hx
  unfold setCap at hx
  dsimp only at hx
  cases hk : σ.kheap o with
  | none =>
    have : getObject (Z := Unit) o σ = (∅, True) := by
      simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt, NonDet.fail]
    rw [nd_bind_apply, this] at hx
    obtain ⟨_, h, _⟩ := hx; exact h.elim
  | some obj =>
    rw [nd_bind_one (Notif.getObject_eq hk)] at hx
    cases obj with
    | cnode sz cn =>
      simp only [] at hx
      split at hx
      · rw [Notif.nd_pure_bind'] at hx
        exact psk_setObject_at hk (Or.inr ⟨_, _, _, rfl, rfl⟩) x hx
      · rw [nd_bind_apply] at hx
        obtain ⟨_, h, _⟩ := hx; exact h.elim
    | tcb tcb =>
      simp only [] at hx
      repeat' split at hx
      all_goals first
        | (rw [nd_bind_apply] at hx; obtain ⟨_, h, _⟩ := hx; exact h.elim)
        | (rw [Notif.nd_pure_bind'] at hx
           exact psk_setObject_at hk (o' := _) (by exact Or.inl ⟨_, _, rfl, rfl, rfl, rfl⟩) x hx)
    | _ =>
      simp only [] at hx
      rw [nd_bind_apply] at hx
      obtain ⟨_, h, _⟩ := hx; exact h.elim

theorem psk_doExtendedOp (eop : DetExtMonad Unit) : PSK (doExtendedOp (Z := Unit) eop) := by
  intro σ x hx
  rw [doExtendedOp_unit] at hx
  rw [Set.mem_singleton_iff.1 hx]; exact SK.refl σ

theorem psk_setCdt (t : Cdt) : PSK (setCdt (Z := Unit) t) := by
  unfold setCdt
  exact psk_get_put fun σ => SK.of_eq rfl rfl rfl rfl rfl rfl

theorem psk_setOriginal (sl : CslotPtr) (v : Bool) : PSK (setOriginal (Z := Unit) sl v) := by
  intro σ x hx
  rw [setOriginal_eq] at hx
  rw [Set.mem_singleton_iff.1 hx]; exact SK.of_eq rfl rfl rfl rfl rfl rfl

theorem psk_capInsert (c : Cap) (src dest : CslotPtr) : PSK (capInsert (Z := Unit) c src dest) := by
  unfold capInsert setUntypedCapAsFull updateCdt
  repeat (first | exact psk_getCap _ | exact psk_setCap _ _ | exact psk_doExtendedOp _ | exact psk_setCdt _ |
    exact psk_setOriginal _ _ | exact psk_pure _ | exact psk_pure' _ | exact psk_gets _ | exact psk_assert _ |
    (refine psk_bind ?_ (fun _ => ?_)) | (apply psk_ite))

theorem psk_checkCapAt (c : Cap) (sl : CslotPtr) {m : SMonad Unit Unit} (hm : PSK m) :
    PSK (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt NonDet.when
  exact psk_bind (psk_getCap sl) fun _ => psk_ite _ hm (psk_pure' _)

/-! ### The spec's `empty_slot` of a TCB slot -/

theorem getCap_tcb_three {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    getCap (Z := Unit) (t, tcbCnodeIndex 3) σ = ({(x.tcbFaultHandler, σ)}, False) := by
  unfold getCap
  dsimp only
  rw [nd_bind_one (Notif.getObject_eq hk)]
  dsimp only
  rw [Notif.nd_pure_bind']
  have : tcbCnodeMap x (tcbCnodeIndex 3) = some x.tcbFaultHandler := by
    unfold tcbCnodeMap
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  rw [this]; rfl

/-- **The spec's `empty_slot` of the fault-handler slot** of a TCB holding a
cap: one outcome, `SK`. -/
theorem emptySlot_tcb {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hc : x.tcbFaultHandler ≠ .nullCap) :
    ∃ σ', emptySlot (Z := Unit) (t, tcbCnodeIndex 3) .nullCap σ = ({((), σ')}, False) ∧ SK σ σ' := by
  set sl : CslotPtr := (t, tcbCnodeIndex 3)
  set cd : Cdt := Function.update (fun p => if σ.cdt p = some sl then σ.cdt sl else σ.cdt p) sl none with hcd
  set σa : State Unit := { σ with cdt := cd } with hσa
  set σb : State Unit := { σa with isOriginalCap := Function.update σa.isOriginalCap sl false } with hσb
  have hkb : σb.kheap t = some (.tcb x) := hk
  refine ⟨setTcbSlot σb t x 3 .nullCap, ?_, ?_⟩
  · unfold emptySlot
    rw [nd_bind_one (getCap_tcb_three hk), if_neg hc]
    rw [Notif.nd_gets_bind, Notif.nd_gets_bind, Notif.nd_pure_bind']
    have h1 : setCdt (Z := Unit) cd σ = ({((), σa)}, False) := by
      unfold setCdt
      rw [nd_bind_single (show (NonDet.get : NonDet (State Unit) (State Unit)) σ = ({(σ, σ)}, False) from rfl)]
      rfl
    rw [nd_bind_one h1, nd_bind_one (doExtendedOp_unit _ σa), nd_bind_one (setOriginal_eq sl false σa),
      nd_bind_one (setCap_tcb (Z := Unit) .nullCap hkb (by decide))]
    rfl
  · have e : SK σ σb := SK.of_eq rfl rfl rfl rfl rfl rfl
    refine e.trans (SK.upd hkb (Or.inl ⟨x, _, rfl, rfl, ?_, ?_⟩)) <;> simp [tcbSet]

theorem liftE_mem_inv {σ ε α : Type} {m : NonDet σ α} {s : σ} {y : Except ε α × σ}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y.2 = x.2 := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨x, hx, rfl⟩

/-- **An Ok outcome of the spec's fault-handler install** over a slot
holding the null cap or a trivially deleted (non-final) cap is `SK`
(`capDelete_triv`, `emptySlot_tcb`, then `check_cap_at` and `cap_insert`). -/
theorem install_sk {σ1 σ2 : State Unit} {p : ObjRef} {x : Tcb} (hk : σ1.kheap p = some (.tcb x))
    (ssl : CslotPtr) (fh : Cap × CslotPtr)
    (hold : x.tcbFaultHandler = .nullCap ∨ (x.tcbFaultHandler ≠ .nullCap ∧
      ∃ c, x.tcbFaultHandler = absCap c ∧ c ≠ .Null ∧ TrivKind σ1 c false))
    (hx : (.ok (), σ2) ∈ ((installTcbCap (Z := Unit) p ssl 3 (some fh)).run σ1).1) : SK σ1 σ2 := by
  obtain ⟨σe, hde, hske⟩ : ∃ σe, (capDelete (Z := Unit) (p, tcbCnodeIndex 3)).run σ1 = ({(.ok (), σe)}, False) ∧
      SK σ1 σe := by
    rcases hold with h0 | ⟨hn, c, hc, hcn, ht⟩
    · refine ⟨σ1, capDelete_null ?_, SK.refl _⟩
      rw [getCap_tcb_three hk, h0]
    · obtain ⟨σe, he, hs⟩ := emptySlot_tcb hk hn
      exact ⟨σe, capDelete_triv _ σ1 σe (getCap_tcb_three hk) (Or.inr ⟨c, false, hc, hcn, ht⟩) he, hs⟩
  obtain ⟨nc, sl⟩ := fh
  unfold installTcbCap at hx
  dsimp only at hx
  rw [run_bind_ok_st hde] at hx
  unfold NonDetE.unlessE at hx
  split at hx
  · have : σ2 = σe := by
      have hx' : ((.ok (), σ2) : Except Unit Unit × State Unit) ∈ ({(.ok (), σe)} : Set _) := hx
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 hx')).2
    rw [this]; exact hske
  · obtain ⟨z, hz, e⟩ := liftE_mem_inv hx
    simp only at e
    rw [e]
    exact hske.trans (psk_checkCapAt _ _ (psk_checkCapAt _ _ (psk_capInsert _ _ _)) σe z hz)

/-! ### What `SK` keeps -/

theorem SK.blkQ {σ σ' : State Unit} (h : SK σ σ') {t : ObjRef} {ts : ThreadState} (hq : BlkQ σ t ts) :
    BlkQ σ' t ts := by
  have hm : ∀ u, (∃ xu, σ.kheap u = some (.tcb xu)) → ∃ xu, σ'.kheap u = some (.tcb xu) := by
    rintro u ⟨xu, hxu⟩
    obtain ⟨y, hy, -⟩ := h.vk.tcb u xu hxu
    exact ⟨y, hy⟩
  obtain ⟨hE, hN⟩ := hq
  refine ⟨fun e he => ?_, fun n hn => ?_⟩
  · obtain ⟨ep, hke, h1, h2, h3⟩ := hE e he
    exact ⟨ep, h.ep _ _ hke, h1, h2, fun u hu hut => hm u (h3 u hu hut)⟩
  · obtain ⟨xn, hkn, h1, h2, h3⟩ := hN n hn
    exact ⟨xn, h.ntfn _ _ hkn, h1, h2, fun u hu hut => hm u (h3 u hu hut)⟩

theorem SK.bindOK {σ σ' : State Unit} (h : SK σ σ') {t c : ObjRef} (hb : BindOK σ t c) : BindOK σ' t c := by
  obtain ⟨x, y, n, hkt, hxs, hkc, hyt, hne, hnot, hrq, hnc, hrel, hA⟩ := hb
  have hv := h.vk
  obtain ⟨xb, hkb, -, hsb⟩ := hv.tcb t x hkt
  have hnot' : ∀ u xu, σ'.kheap u = some (.tcb xu) → xu.tcbSchedContext ≠ some c := by
    intro u xu hu
    obtain ⟨x0, hx0⟩ := hv.tcb' u xu hu
    obtain ⟨y', hy', -, hsc'⟩ := hv.tcb u x0 hx0
    rw [hu] at hy'; cases hy'
    rw [hsc']; exact hnot u x0 hx0
  refine ⟨xb, y, n, hkb, by rw [hsb, hxs], (hv.sc c y n).2 hkc, hyt, hne, hnot', by rw [h.rdq]; exact hrq,
    by rw [hv.ct]; exact hnc, fun u hu => ?_, hv.actReady hA⟩
  rw [hv.rq] at hu
  obtain ⟨xu, cu, yu, nu, h1, h2, h3, h4⟩ := hrel u hu
  obtain ⟨xu', h1', -, h2'⟩ := hv.tcb u xu h1
  exact ⟨xu', cu, yu, nu, h1', by rw [h2', h2], (hv.sc cu yu nu).2 h3, h4⟩

/-- A thread blocked on an endpoint is in its queue (l4v `sym_refs`). -/
def BlkIn (σ : State Unit) (p : ObjRef) (ts : ThreadState) : Prop :=
  ∀ e, epBlocked ts = some e → ∃ ep, σ.kheap e = some (.endpoint ep) ∧ p ∈ ep.epQueue

/-- **The spec's facts the scheduler step of SetSchedParams needs** of the
target `p` (`schedTailHyp_of`'s `hI`, `scSpecHyp_of`'s `hS2`,
`bindSpecHyp_of`'s `hB2`). -/
def SpecPost (σ : State Unit) (p : ObjRef) (sco : Option (Option ObjRef)) : Prop :=
  ∃ x, σ.kheap p = some (.tcb x) ∧ Notif.ActReady σ ∧ BlkQ σ p x.tcbState ∧ BlkIn σ p x.tcbState ∧
    (sco = some none → ∃ c y n, x.tcbSchedContext = some c ∧ σ.kheap c = some (.schedContext y n) ∧
      y.scTcb = some p) ∧
    (∀ v, sco = some (some v) → BindOK σ p v)

theorem SpecPost.sk {σ σ' : State Unit} {p : ObjRef} {sco : Option (Option ObjRef)} (h : SpecPost σ p sco)
    (hs : SK σ σ') : SpecPost σ' p sco := by
  obtain ⟨x, hk, hA, hQ, hIn, hU, hB⟩ := h
  obtain ⟨y, hy, hst, hsc⟩ := hs.vk.tcb p x hk
  refine ⟨y, hy, hs.vk.actReady hA, by rw [hst]; exact hs.blkQ hQ, fun e he => ?_, fun e => ?_,
    fun v e => hs.bindOK (hB v e)⟩
  · rw [hst] at he
    obtain ⟨ep, hke, hm⟩ := hIn e he
    exact ⟨ep, hs.ep _ _ hke, hm⟩
  obtain ⟨c, z, n, h1, h2, h3⟩ := hU e
  exact ⟨c, z, n, by rw [hsc, h1], (hs.vk.sc c z n).2 h2, h3⟩

theorem restart_fields {σ σ1 : State Unit} {ct : ObjRef} {x : Tcb} (hk : σ.kheap ct = some (.tcb x))
    (h : setThreadState (Z := Unit) ct .restart σ = ({((), σ1)}, False)) :
    σ1.readyQueues = σ.readyQueues ∧ σ1.releaseQueue = σ.releaseQueue ∧ σ1.curThread = σ.curThread := by
  rw [setThreadState_eq' hk] at h
  have e := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h))).2
  subst e
  unfold Notif.stsAct
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- **`SpecPost` after the caller's restart**, from the scheduler invariant
`Inv` and the decoder's checks (`ScDec`): the target's `BlkQ`; an unbind's
SC points back (`Inv.back`); a bind's SC is unbound with refills
(`Inv.ne`), no TCB names it (`Inv.back`), the target (with no SC) is in no
ready queue (`Inv.rq`) and not current (`hpc`), the release queue's members
are bound (`Inv.rel`). -/
theorem specPost_restart {σ σ1 : State Unit} (hI : Inv σ) {ct : ObjRef} {xc : Tcb}
    (hkc : σ.kheap ct = some (.tcb xc)) (hrun : runnable xc.tcbState = true)
    (hst1 : setThreadState (Z := Unit) ct .restart σ = ({((), σ1)}, False))
    {p : ObjRef} {sco : Option (Option ObjRef)} (hD : ScDec σ p sco)
    (hQ : ∀ x, σ.kheap p = some (.tcb x) → BlkQ σ p x.tcbState ∧ BlkIn σ p x.tcbState)
    (hpc : ∀ v, sco = some (some v) → p ≠ σ.curThread) : SpecPost σ1 p sco := by
  obtain ⟨x, hkp, hU, hB⟩ := hD
  have hk1 := restart_kheap hkc hst1
  obtain ⟨hrq1, hrl1, hct1⟩ := restart_fields hkc hst1
  obtain ⟨x1, hkp1, hQ1⟩ := blkQ_restart hkc hst1 hkp (hQ x hkp).1
  have hsc1 : x1.tcbSchedContext = x.tcbSchedContext := by
    rw [hk1] at hkp1
    by_cases e : p = ct
    · subst e; rw [Function.update_self] at hkp1; cases hkp1
      rw [hkc] at hkp; cases hkp; rfl
    · rw [Function.update_of_ne e, hkp] at hkp1; cases hkp1; rfl
  have hIn1 : BlkIn σ1 p x1.tcbState := by
    have hk1' := hkp1
    rw [hk1] at hk1'
    by_cases e : p = ct
    · subst e; rw [Function.update_self] at hk1'; cases hk1'
      intro e' he'; simp [epBlocked] at he'
    · rw [Function.update_of_ne e, hkp] at hk1'; cases hk1'
      intro e' he'
      obtain ⟨ep, hke, hm⟩ := (hQ x hkp).2 e' he'
      have hne : e' ≠ ct := by rintro rfl; rw [hkc] at hke; cases hke
      exact ⟨ep, by rw [hk1, Function.update_of_ne hne]; exact hke, hm⟩
  have hko : ∀ q, (∀ z, σ.kheap q ≠ some (.tcb z)) → σ1.kheap q = σ.kheap q := fun q hq => by
    rw [hk1, Function.update_of_ne]; rintro rfl; exact hq xc hkc
  have hksc : ∀ q y n, σ.kheap q = some (.schedContext y n) → σ1.kheap q = some (.schedContext y n) :=
    fun q y n h => by rw [hko q (fun z hz => by rw [h] at hz; cases hz)]; exact h
  have hA1 := actReady_restart hI.actReady hkc hrun hst1
  have htcb1 : ∀ u xu, σ1.kheap u = some (.tcb xu) → ∃ x0, σ.kheap u = some (.tcb x0) ∧
      xu.tcbSchedContext = x0.tcbSchedContext := by
    intro u xu hu
    rw [hk1] at hu
    by_cases e : u = ct
    · subst e; rw [Function.update_self] at hu; cases hu; exact ⟨xc, hkc, rfl⟩
    · rw [Function.update_of_ne e] at hu; exact ⟨xu, hu, rfl⟩
  have htcb1' : ∀ u x0, σ.kheap u = some (.tcb x0) → ∃ xu, σ1.kheap u = some (.tcb xu) ∧
      xu.tcbSchedContext = x0.tcbSchedContext := by
    intro u x0 hu
    by_cases e : u = ct
    · subst e; rw [hkc] at hu; cases hu; exact ⟨{ xc with tcbState := .restart }, by rw [hk1, Function.update_self], rfl⟩
    · exact ⟨x0, by rw [hk1, Function.update_of_ne e]; exact hu, rfl⟩
  refine ⟨x1, hkp1, hA1, hQ1, hIn1, fun e => ?_, fun v e => ?_⟩
  · obtain ⟨-, hn⟩ := hU e
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hn
    obtain ⟨y, n, hky, hyt⟩ := hI.back p x c hkp hc
    exact ⟨c, y, n, by rw [hsc1, hc], hksc c y n hky, hyt⟩
  · obtain ⟨hx0, y, n, hky, hyt, -⟩ := hB v e
    refine ⟨x1, y, n, hkp1, by rw [hsc1, hx0], hksc v y n hky, hyt, hI.ne v y n hky, fun u xu hu he => ?_,
      fun d pr hm => ?_, by rw [hct1]; exact hpc v e, fun u hu => ?_, hA1⟩
    · obtain ⟨x0, hx0', e0⟩ := htcb1 u xu hu
      obtain ⟨y', n', hky', hyt'⟩ := hI.back u x0 v hx0' (by rw [← e0]; exact he)
      rw [hky] at hky'; cases hky'
      rw [hyt] at hyt'; cases hyt'
    · rw [hrq1] at hm
      obtain ⟨x', scp, -, -, h1, h2, -⟩ := hI.rq d pr p hm
      rw [hkp] at h1; cases h1
      rw [hx0] at h2; cases h2
    · rw [hrl1] at hu
      obtain ⟨xu, cu, yu, nu, h1, h2, -, h4, -⟩ := hI.rel u hu
      obtain ⟨xu', h1', e'⟩ := htcb1' u xu h1
      exact ⟨xu', cu, yu, nu, h1', by rw [e', h2], hksc cu yu nu h4, hI.ne cu yu nu h4⟩

end Spec

end

end Fl4Proofs.P3.Sched
