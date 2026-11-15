/-
P3 (DESIGN.md §9), scheduling contexts: **SchedContext invocation decode**
against l4v `decode_sched_context_invocation` (Fl4Spec/Decode.lean), the
labels' checks and their invocations.

* `McpRel`: each TCB's `MCP` word is its `tcb_mcpriority` (read by the
  YieldTo check; kept by everything here, which writes no `MCP` word);
* `ScQ`: after a successful decode, l4v's `set_thread_state Restart`, the
  invocation, and `handle_invocation`'s reply and `set_thread_state Running`
  when the invocation returns data;
* `yieldto_branch_refines`: the YieldTo label (the checks of
  `decode_sched_context_yield_to`, then `yieldto_invoke_refines`), ending in
  `ActIdle` too;
* `KRels`, `RFoot`: the branches' footprints (`KFoot` for Bind,
  UnbindObject, Consumed; `TFoot` for YieldTo; `RFoot` for Unbind) and the
  spec's `SOK` (ScPres.lean), from which ScDecodeAll.lean's
  `sc_decode_refines` frames the other relations.
-/
import Fl4Proofs.P3.ScYieldTo
import Fl4Proofs.P3.ScDecode
import Fl4Proofs.P3.ScCallUnlink
import Fl4Proofs.P3.ScPresOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- The `MCP` word of the TCB at `t`. -/
def mcpA (t : U64) : U64 := core.num.U64.wrapping_add t 3440#u64

theorem obj.Tcb.mcp.spec' (s : S) (t : obj.Tcb) : obj.Tcb.mcp st t s ⦃ v => v = L.mem s (mcpA t) ⦄ := by
  unfold obj.Tcb.mcp; step*; simp_all [mcpA, layout.tcb.MCP, layout.tcb.F]

/-- **The MCP relation**: each TCB's `MCP` word is its `tcb_mcpriority`. -/
def McpRel (T : Set U64) (m : U64 → U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ (m (mcpA t)).val = x.tcbMcpriority.toNat

theorem w8_gt_iff {p q : U64} {x y : Fl4Spec.Priority} (hp : p.val = x.toNat) (hq : q.val = y.toNat) :
    p > q ↔ x > y := by
  rw [gt_iff_lt, gt_iff_lt, BitVec.lt_def, ← hp, ← hq]; exact Iff.rfl

/-! ### Running the spec's decoders -/

theorem wE_pos {α : Type} {P : Prop} [Decidable P] (h : P) (e : Fl4Spec.SyscallError)
    (f : Unit → Fl4Spec.SEMonad Unit α) (s : Fl4Spec.State Unit) :
    (Fl4Spec.NonDetE.whenE P (Fl4Spec.NonDetE.throwError e) >>= f).run s = ({(.error e, s)}, False) := by
  unfold Fl4Spec.NonDetE.whenE; rw [ite_eq_left h]
  exact run_bind_error (σ := Fl4Spec.State Unit) (m := Fl4Spec.NonDetE.throwError e) (s := s) rfl f

theorem wE_neg {α : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : Fl4Spec.SEMonad Unit Unit)
    (f : Unit → Fl4Spec.SEMonad Unit α) (s : Fl4Spec.State Unit) :
    (Fl4Spec.NonDetE.whenE P m >>= f).run s = (f ()).run s := by
  unfold Fl4Spec.NonDetE.whenE; rw [ite_eq_right h]
  exact run_bind_ok (σ := Fl4Spec.State Unit) (m := Fl4Spec.NonDetE.returnOk ()) (s := s) (a := ()) rfl f

theorem lE_bind {α β : Type} {m : Fl4Spec.SMonad Unit α} {s : Fl4Spec.State Unit} {a : α}
    (h : m s = ({(a, s)}, False)) (f : α → Fl4Spec.SEMonad Unit β) :
    (Fl4Spec.NonDetE.liftE m >>= f).run s = (f a).run s :=
  run_bind_ok (run_liftE h) f

/-- After a successful decode: l4v's `set_thread_state Restart`, the
invocation, and (when it returns data) `handle_invocation`'s reply (if
`call`) and `set_thread_state Running`; `Rels` of FL4's state and the
spec's after. -/
def ScQ (Rels : S → Fl4Spec.State Unit → Prop) (σ : Fl4Spec.State Unit) (ct : U64) (call : Bool)
    (inv : Fl4Spec.SchedContextInvocation) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  res.1 = .Ok () ∧ ∃ (σ0 : Fl4Spec.State Unit) (data : List Fl4Spec.Data) (σ1 σ2 : Fl4Spec.State Unit),
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
    Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({(data, σ1)}, False) ∧
    ((data = [] ∧ σ2 = σ1) ∨
      (do
        Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, data))
        Fl4Spec.setThreadState (Z := Unit) ct.bv .running : Fl4Spec.SMonad Unit Unit) σ1 = ({((), σ2)}, False)) ∧
    Rels res.2.1 σ2

/-- The relations after a YieldTo or Consumed invocation. -/
def YRels (N T C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  SchedRel st N T C c s σ ∧ NtfnStateRel N T (L.mem s) σ ∧ NSC N C σ ∧ Inv σ ∧ YieldRel T C (L.mem s) σ ∧
    ActIdle σ

theorem illegal_ok (s : S) (a : A) (P : core.result.Result Unit error.Exc × S × A → Prop)
    (h : P (.Err (.Sys .IllegalOperation), s, a)) :
    (do let r ← error.illegal Unit; ok (r, s, a)) ⦃ P ⦄ := by
  simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).mpr h

/-- **The YieldTo label**: FL4's checks (the SC's thread, not the caller,
priority at most the caller's MCP, the caller yielding to nothing) are
`decode_sched_context_yield_to`'s, and the invocation is
`yieldto_invoke_refines`'s. `hback` is the SC→TCB back-pointer (a bound
thread of `T` whose SC word is `sc`); `hcs`: the caller is schedulable. -/
theorem yieldto_branch_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {sc : U64} (hsc : sc ∈ C)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ T ∧ L.mem s (scA (L.mem s (scW sc 24#u64))) = sc)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (call : Bool)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c) :
    (do
      let i1 ← obj.Sc.tcb st sc s
      let b ← obj.Tcb.is_null i1
      if b
      then let r ← error.illegal Unit
           ok (r, s, a)
      else
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq i1 ct
        if b1
        then let r ← error.illegal Unit
             ok (r, s, a)
        else
          let i2 ← obj.Tcb.prio st i1 s
          let i3 ← obj.Tcb.mcp st ct s
          if i2 > i3
          then let r ← error.illegal Unit
               ok (r, s, a)
          else
            let i4 ← obj.Tcb.yield_to st ct s
            if i4 != 0#u64
            then let r ← error.illegal Unit
                 ok (r, s, a)
            else
              let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
              let (s3, a2) ← schedcontext.yield_to st ar s2 a sc call
              ok (core.result.Result.Ok (), s3, a2)) ⦃ res =>
      CPost σ (Fl4Spec.decodeSchedContextYieldTo (Z := Unit) sc.bv) s a
        (ScQ (fun s' σ' => YRels (st := st) N T C c s' σ' ∧ WritesIn st s s' (TFoot st T N C c s σ) ∧
          SOK (false, true) σ σ') σ ct call) res ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have hsc0 := hC0 sc hsc
  obtain ⟨xc, hkc, -, -, -, hpc⟩ := hs.tcb ct hct
  have hxtw : x.scTcb = optRef (L.mem s (scW sc 24#u64)) := hx.tcb
  have hill : ∀ (P : Prop) [Decidable P], P → ∀ f : Unit → Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation,
      (Fl4Spec.NonDetE.whenE P (Fl4Spec.NonDetE.throwError .illegalOperation) >>= f).run σ =
        ({(.error .illegalOperation, σ)}, False) := fun P _ h f => wE_pos h _ f σ
  step with obj.Sc.tcb.spec as ⟨i1, hi1⟩
  rw [scTcbA_eq] at hi1
  subst hi1
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  subst hb
  by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
    refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
    unfold Fl4Spec.decodeSchedContextYieldTo
    rw [lE_bind (getScObjRef_eq hk _), hxtw, h0, optRef_zero]
    exact hill _ rfl _
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨ht, hts⟩ := hback h0
  set t := L.mem s (scW sc 24#u64) with htdef
  have htc : x.scTcb = some t.bv := by rw [hxtw, optRef_ne h0]
  obtain ⟨xt, hkt, -, -, hxts, hpt⟩ := hs.tcb t ht
  have hxt : xt.tcbSchedContext = some sc.bv := by rw [hxts, hts, optRef_ne hsc0]
  have hpre : ∀ f : Option Fl4Spec.ObjRef → Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation,
      (Fl4Spec.NonDetE.liftE (Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scTcb sc.bv) >>= f).run σ =
        (f (some t.bv)).run σ := fun f => by rw [lE_bind (getScObjRef_eq hk _), htc]
  step as ⟨b1, hb1⟩
  by_cases hte : t = ct
  · have : b1 = true := by rw [hb1]; simpa using hte
    simp only [this, ↓reduceIte]
    refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
    unfold Fl4Spec.decodeSchedContextYieldTo
    rw [hpre, wE_neg (by simp), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
      ({(σ.curThread, σ)}, False) from rfl), hcur, ← hte]
    exact hill _ rfl _
  have : b1 = false := by rw [hb1]; simpa using hte
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have hne' : t.bv ≠ ct.bv := bv_ne hte
  obtain ⟨xm, hkm, hmc⟩ := hM ct hct
  rw [hkc] at hkm; cases hkm
  obtain ⟨xy, hky, hyc⟩ := hY.tcb ct hct
  rw [hkc] at hky; cases hky
  have hpre2 : ∀ f : Fl4Spec.Priority → Fl4Spec.Priority → Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation,
      (Fl4Spec.decodeSchedContextYieldTo (Z := Unit) sc.bv).run σ =
        (Fl4Spec.NonDetE.whenE (xt.tcbPriority > xc.tcbMcpriority)
          (Fl4Spec.NonDetE.throwError .illegalOperation) >>= fun _ => do
          let ytPtr ← Fl4Spec.NonDetE.liftE <| Fl4Spec.threadGet (Z := Unit) Fl4Spec.Tcb.tcbYieldTo ct.bv
          Fl4Spec.NonDetE.whenE (ytPtr ≠ none) <| Fl4Spec.NonDetE.throwError .illegalOperation
          Fl4Spec.NonDetE.returnOk <| .invokeSchedContextYieldTo sc.bv).run σ := by
    intro _
    unfold Fl4Spec.decodeSchedContextYieldTo
    rw [hpre, wE_neg (by simp), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
      ({(σ.curThread, σ)}, False) from rfl), hcur, wE_neg (by simpa using hne'),
      show Fl4Spec.the (some t.bv) = t.bv from rfl, lE_bind (threadGet_eq _ hkt), lE_bind (threadGet_eq _ hkc)]
  step with obj.Tcb.prio.spec as ⟨i2, hi2⟩
  step with obj.Tcb.mcp.spec' as ⟨i3, hi3⟩
  subst hi2 hi3
  by_cases hgt : L.mem s (prioA t) > L.mem s (mcpA ct)
  · simp only [hgt, ↓reduceIte]
    refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
    rw [hpre2 (fun _ _ => default)]
    exact hill _ ((w8_gt_iff hpt hmc).1 hgt) _
  simp only [hgt, ↓reduceIte]
  have hpre3 := hpre2 (fun _ _ => default)
  rw [wE_neg (fun h => hgt ((w8_gt_iff hpt hmc).2 h)), lE_bind (threadGet_eq _ hkc)] at hpre3
  step with obj.Tcb.yield_to.spec as ⟨i4, hi4⟩
  subst hi4
  by_cases hy0 : L.mem s (yieldA ct) = 0#u64
  swap
  · have : (L.mem s (yieldA ct) != 0#u64) = true := by simp [hy0]
    simp only [this, ↓reduceIte]
    refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
    rw [hpre3]
    exact hill _ (by rw [hyc, optRef_ne hy0]; simp) _
  have : (L.mem s (yieldA ct) != 0#u64) = false := by simp [hy0]
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have hyn : xc.tcbYieldTo = none := by rw [hyc, hy0, optRef_zero]
  rw [wE_neg (by simp [hyn])] at hpre3
  refine WP.spec_mono (yieldto_invoke_refines s a σ hS hR hN hI hY hC0 hsc hk ht htc hkt hxt hct
    (Ne.symm hte) hcur hkc hyn hcs hAI call hmb hmax htu hmsg) ?_
  rintro r ⟨h1, -, σ0, data, σ1, σ2, he0, hyt, hcase, hS', hR', hN', hI', hY', hA', hw'⟩
  have hsok : SOK (false, true) σ σ2 := by
    refine ((pres_setThreadState _ _ _).of_eq he0).trans (((pres_schedContextYieldTo _).of_eq hyt).trans ?_)
    rcases hcase with ⟨-, rfl⟩ | h
    · exact SOK.refl _ _
    · exact (pres_bind (pres_when _ (pres_replyFromKernel _ _ _)) fun _ => pres_setThreadState _ _ _).of_eq h
  exact Or.inr ⟨.invokeSchedContextYieldTo sc.bv, hpre3, h1, σ0, data, σ1, σ2, he0, hyt, hcase,
    ⟨hS', hR', hN', hI', hY', hA'⟩, hw', hsok⟩


/-- A word the notification code writes is a notification's or a TCB's. -/
theorem nwrite_range {N T : Set U64} (hP : NPlaced T N) {a : U64} (h : NWrite N T a) :
    (∃ n ∈ N, n.val ≤ a.val ∧ a.val < n.val + 40) ∨ (∃ t ∈ T, t.val ≤ a.val ∧ a.val < t.val + 4096) := by
  rcases h with h | ⟨t, ht, e⟩
  · exact Or.inl h
  · refine Or.inr ⟨t, ht, ?_⟩
    have hta := hP.tcb t ht
    rcases e with rfl | rfl | rfl | rfl | rfl
    · rw [tStA_eq, tfield_val hta (by simp)]; simp
    · rw [tBlockA_eq, tfield_val hta (by simp)]; simp
    · rw [badgeRegA_eq, tfield_val hta (by simp)]; simp
    · rw [nextEp_eq, tfield_val hta (by simp)]; simp
    · rw [prevEp_eq, tfield_val hta (by simp)]; simp

/-- Writes of notification words and an SC's `NTFN` word keep the
call-stack words. -/
theorem callWords_of_nwfoot {N T C R : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) {sc : U64} (hsc : sc ∈ C)
    (hw : WritesIn st s s' (fun b => NWrite N T b ∨ b = scW sc 40#u64)) :
    (∀ q ∈ C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have hb := hx.bounds
  have hv40 : (scW sc 40#u64).val = sc.val + 40 := by rw [scW_val (by simp; omega)]; rfl
  have h40 : ScObj sc n (scW sc 40#u64) := hx.in_obj (by unfold ScIn; rw [hv40]; omega)
  have hw' : ∀ b, Aligned b → ¬ NWrite N T b → b ≠ scW sc 40#u64 → L.mem s' b = L.mem s b :=
    fun b hb' h1 h2 => hw.mem_eq hb' (fun h => h.elim h1 h2)
  refine ⟨fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨xq, nq, hkq, hxq⟩ := hs.scs q hq
    have ha := hxq.hdr (K := 32#u64) (by simp) (by simp)
    obtain ⟨h1, -, -, -⟩ := hS.scOutIn hq ha.2
    rw [scReplyA_eq]
    refine hw' _ ha.1 h1 ?_
    intro e
    by_cases eq : q = sc
    · subst eq; have := congrArg UScalar.val e; rw [hv40, scW_val (by have := hxq.bounds; simp; omega)] at this
      simp at this
    · exact hS.scDisj q hq sc hsc eq xq nq x n hkq hk _ (hxq.in_obj ha.2) (e ▸ h40)
  · have hA := hRP.align r hr
    have v1 := rPrevA_val hA
    have v2 := rNextA_val hA
    have hfar := hRP.sc r hr sc hsc x n hk
    unfold ScObj at h40
    have hnw : ∀ a : U64, (a.val = r.val + 8 ∨ a.val = r.val + 16) → ¬ NWrite N T a := by
      intro a ha hn
      rcases nwrite_range hS.placed hn with ⟨m, hm, g1, g2⟩ | ⟨y, hy, g1, g2⟩
      · have := hRP.ntfn r hr m hm; omega
      · have := hRP.tcb r hr y hy; omega
    refine ⟨hw' _ (hRP.aligned hr (Or.inl v1)) (hnw _ (Or.inl v1)) ?_,
      hw' _ (hRP.aligned hr (Or.inr v2)) (hnw _ (Or.inr v2)) ?_⟩
    · intro e; have := congrArg UScalar.val e; omega
    · intro e; have := congrArg UScalar.val e; omega

/-- The call-stack relation and the replies' placement across a step that
keeps the call-stack words and what the relation reads of the spec. -/
theorem CallRel.carry {N T C R : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hcw : (∀ q ∈ C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
      (∀ r ∈ R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)))
    (hksb : L.ksb s' = L.ksb s) (hk : CKeep σ σ') :
    CallRel (L.mem s') R C σ' Lst ∧ RPlaced st N T C R c s' σ' :=
  ⟨hCR.frame hcw.1 hcw.2 (fun q _ y n hy => hk.1 _ y n hy)
    (fun d _ x hx => let ⟨x', h1, h2, _⟩ := hk.2.1 _ x hx; ⟨x', h1, h2⟩), hRP.frame hksb hk.2.2⟩

/-- `RFree` across such a step. -/
theorem RFree.carry {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : RFree m R C σ Lst) (hCR : CallRel m R C σ Lst)
    (hcw : ∀ r ∈ R, m' (rPrevA r) = m (rPrevA r) ∧ m' (rNextA r) = m (rNextA r)) (hk : CKeep σ σ') :
    RFree m' R C σ' Lst :=
  h.frame hcw fun d hd ⟨x', hk', hx'⟩ => by
    obtain ⟨x, hkx, -⟩ := hCR.reply d hd
    obtain ⟨x2, hk2, -, e2⟩ := hk.2.1 _ x hkx
    rw [hk'] at hk2; cases hk2
    exact ⟨x, hkx, e2 ▸ hx'⟩

/-- The scheduler relations after a SchedContext invocation. -/
def SRels (N T C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  SchedRel st N T C c s σ ∧ NtfnStateRel N T (L.mem s) σ ∧ NSC N C σ ∧ Inv σ

/-- `SRels`, and the writes since `(s0, σ0)` in `KFoot`. -/
def KRels (N T C : Set U64) (c : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  SRels (st := st) N T C c s σ ∧ WritesIn st s0 s (KFoot st T N C c s0 σ0) ∧ SOK (true, true) σ0 σ

/-- The reply words: replies' `NEXT` words, SCs' `REPLY` words. -/
def RW (R C : Set U64) (b : U64) : Prop := (∃ r ∈ R, b = rNextA r) ∨ (∃ q ∈ C, b = scReplyA q)

/-- **The footprint of Unbind**: `KFoot` and the reply words. -/
def RFoot (st : machine.Store S) [L : LawfulStore st] (T N C R : Set U64) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  KFoot st T N C c s σ b ∨ RW R C b

theorem scNtfn_keep {N T C : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hS' : SchedRel st N T C c s' σ') {sc : U64} (hsc : sc ∈ C)
    (hm : L.mem s' (scW sc 40#u64) = L.mem s (scW sc 40#u64)) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) :
    ∃ y' n', σ'.kheap sc.bv = some (.schedContext y' n') ∧ y'.scNtfn = y.scNtfn := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  obtain ⟨x, m, hkx, hx⟩ := hs.scs sc hsc
  rw [hk] at hkx; cases hkx
  obtain ⟨x', m', hkx', hx'⟩ := hs'.scs sc hsc
  exact ⟨x', m', hkx', by rw [hx'.ntfn, hx.ntfn, hm]⟩

/-- **SchedContext `Unbind`** (the decoder's branch after its check: restart,
`unbind_all_tcbs`, `unbind_ntfn`, `unbind_reply`) refines l4v's
`set_thread_state Restart` and `invoke_sched_context` (`Unbind`), carrying
the call-stack relation to `unbind_reply`. -/
theorem unbind_invoke_refines {N T C R : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) (hpi : sc.bv ≠ Fl4Spec.idleScPtr)
    {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext y n))
    (hbnd : ∀ t : U64, y.scTcb = some t.bv → t ∈ T ∧ t.bv ≠ σ.idleThread)
    (hbn : ∀ m : U64, y.scNtfn = some m.bv → m ∈ N)
    {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hrun : Fl4Spec.runnable xc.tcbState = true) (hRF : RFree (L.mem s) R C σ Lst) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.unbind_all_tcbs st ar s2 a sc
      let s4 ← schedcontext.unbind_ntfn st s3 sc
      let s5 ← schedcontext.unbind_reply st s4 sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ (σ0 σ3 : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
      Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextUnbind sc.bv) σ0 = ({([], σ3)}, False) ∧
      SRels (st := st) N T C c res.2.1 σ3 ∧ CallRel (L.mem res.2.1) R C σ3 Lst' ∧
      RPlaced st N T C R c res.2.1 σ3 ∧ RFree (L.mem res.2.1) R C σ3 Lst' ∧
      WritesIn st s res.2.1 (RFoot st T N C R c s σ) ⦄ := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs sc hsc
  rw [hk] at hk0; cases hk0
  have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
  -- the restart
  have hnb : ∀ m, Fl4Spec.ThreadState.restart ≠ .blockedOnNotification m := fun _ h => by cases h
  refine WP.spec_bind (WP.spec_and (set_thread_state_refines s σ hR hS hct hkc (not_in_ntfnQueue hR hct hkc hrun)
    sched.TS_RESTART .restart (by rw [tsVals.2.1]; rfl) hnb) (set_thread_state_sfoot hS hct _)) ?_
  rintro s1 ⟨⟨σ1, he1, hR1, hS1⟩, hw1⟩
  have hσ1 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he1
  have hko1 : ∀ q, q ≠ ct.bv → σ1.kheap q = σ.kheap q := fun q hq => by rw [hσ1, stsAct_kheap]; simp [updK, hq]
  have hk1 : σ1.kheap sc.bv = some (.schedContext y n) := by rw [hko1 _ hpc]; exact hk
  have hN1 : NSC N C σ1 := by rw [hσ1]; unfold Fl4Proofs.P3.Notif.stsAct; split <;> exact hN.updTcb
  have hI1 : Inv σ1 := by rw [hσ1]; exact hI.restart hkc hrun
  have hck1 : CKeep σ σ1 := by
    rw [hσ1]
    exact (CKeep.updOther hkc (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ _ e => by cases e)).trans
      (CKeep.of_kheap (stsAct_kheap _ _))
  obtain ⟨hCR1, hRP1⟩ := CallRel.carry hCR hRP (callWords_of_sfoot hS hRP hw1) hw1.1 hck1
  have hRF1 := RFree.carry hRF hCR (callWords_of_sfoot hS hRP hw1).2 hck1
  have hid1 : σ1.idleThread = σ.idleThread := by
    rw [hσ1]; unfold Fl4Proofs.P3.Notif.stsAct; split <;> rfl
  -- `unbind_all_tcbs`
  refine WP.spec_bind (unbind_all_tcbs_refines s1 a σ1 hS1 hR1 hN1 hI1 hsc hpi hk1
    (fun t ht => by rw [hid1]; exact hbnd t ht)) ?_
  rintro ⟨s2, a2⟩ ⟨ha2, σ2, he2, hS2, hR2, hN2, hI2, -, hw2, hck2⟩
  simp only at ha2 hS2 hR2 hw2
  subst ha2
  obtain ⟨hCR2, hRP2⟩ := CallRel.carry hCR1 hRP1 (callWords_of_dfoot hS1 hRP1 hsc hw2) hw2.1 hck2
  have hRF2 := RFree.carry hRF1 hCR1 (callWords_of_dfoot hS1 hRP1 hsc hw2).2 hck2
  have hm40 : L.mem s2 (scW sc 40#u64) = L.mem s1 (scW sc 40#u64) := by
    obtain ⟨Q1, R1, hc1, hs1⟩ := hS1.lists
    obtain ⟨x1, n1, hkx1, hx1⟩ := hs1.scs sc hsc
    have ha := hx1.hdr (K := 40#u64) (by simp) (by simp)
    obtain ⟨-, h2, h3, -⟩ := hS1.scOutIn hsc ha.2
    refine hw2.mem_eq ha.1 ?_
    rintro (hb0 | e)
    · rcases hb0.range hc1.tcbs with ⟨t, ht, g1, g2⟩ | ⟨g1, g2⟩
      · have := h3 t ht; omega
      · omega
    · have hb := hx1.bounds
      have := congrArg UScalar.val e
      rw [scW_val (by simp; omega), scW_val (by simp; omega)] at this
      simp at this
  obtain ⟨y2, n2, hk2, hy2⟩ := scNtfn_keep hS1 hS2 hsc hm40 hk1
  -- `unbind_ntfn`
  refine WP.spec_bind (unbind_ntfn_refines s2 σ2 hS2 hR2 hN2 hI2 hsc hsc0 hk2
    (fun m hm => hbn m (hy2 ▸ hm))) ?_
  rintro s3 ⟨σ3, he3, hS3, hR3, hN3, hI3, -, hw3, hck3⟩
  obtain ⟨hCR3, hRP3⟩ := CallRel.carry hCR2 hRP2 (callWords_of_nwfoot hS2 hRP2 hsc hw3) hw3.1 hck3
  have hRF3 := RFree.carry hRF2 hCR2 (callWords_of_nwfoot hS2 hRP2 hsc hw3).2 hck3
  obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
  obtain ⟨y3, n3, hk3, -⟩ := hs3.scs sc hsc
  -- `unbind_reply`
  refine WP.spec_bind (unbind_reply_refines s3 σ3 hS3 hR3 hN3 hI3 hCR3 hRP3 hsc hsc0 hk3 hRF3) ?_
  rintro s4 ⟨σ4, Lst', he4, hS4, hR4, hN4, hI4, hCR4, hRP4, -, hRF4, hw4⟩
  have k1 : WritesIn st s s1 (KFoot st T N C c s σ) := WritesIn.kfoot_of_sfoot hw1
  have k2 := WritesIn.kfoot_trans k1 (SzKeepC.of hck1.2.2)
    (WritesIn.kfoot_of_sfoot_scw hS1 hsc (K := 24#u64) (by simp) (by simp) (by decide) hw2)
  have k3 := WritesIn.kfoot_trans k2 (SzKeepC.of (SzKeep.trans hck1.2.2 hck2.2.2))
    (WritesIn.kfoot_of_nw_scw hS2 hsc (K := 40#u64) (by simp) (by simp) (by decide) hw3)
  have k4 : WritesIn st s s4 (RFoot st T N C R c s σ) := (k3.trans hw4).mono fun b hb => by
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr hb
  refine (WP.spec_ok _).mpr ⟨rfl, σ1, σ4, Lst', he1, ?_, ⟨hS4, hR4, hN4, hI4⟩, hCR4, hRP4, hRF4, k4⟩
  show (Fl4Spec.schedContextUnbindAllTcbs sc.bv >>= _) σ1 = _
  rw [nd_bind_one he2, nd_bind_one he3, nd_bind_one he4]; rfl


section Spec
open Fl4Spec

theorem suff_of_min {y : SchedContext} (h : MIN_BUDGET ≤ (refillHd y).rAmount) :
    refillSufficient 0 (refillHd y) = true := by
  unfold refillSufficient refillCapacity
  have h0 : ¬ (refillHd y).rAmount < 0 := by rw [BitVec.lt_def]; simp
  simp only [h0, ↓reduceIte, decide_eq_true_eq]
  have e : (refillHd y).rAmount - 0 = (refillHd y).rAmount := by bv_omega
  rw [e]; exact h

/-- Under `Inv`, an active SC's head is sufficient. -/
theorem Inv.suff {σ : State Unit} (h : Inv σ) {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (ha : scActive y = true) :
    refillSufficient 0 (refillHd y) = true := by
  by_cases hp : y.scPeriod = 0
  · exact suff_of_min (h.rr p y n hk ha hp).2.2
  · exact suff_of_min (h.refills p y n hk ha hp).2.2.2

theorem getScReleased_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    getScReleased (Z := Unit) p σ = ({(scReleased σ.curTime x, σ)}, False) := by
  have hr : readScRefillReady (Z := Unit) p σ = some (refillReady σ.curTime (refillHd x)) := by
    show Option.bind (readRefillHead p σ) (fun h => Option.bind (Lookup.asks (fun s : State Unit => s.curTime) σ)
      (fun ct => Lookup.oreturn (refillReady ct h) σ)) = _
    rw [readRefillHead_eq hk hne]; rfl
  have ha : readScActive (Z := Unit) p σ = some (scActive x) := by
    show Option.bind (readSchedContext p σ) (fun sc => Lookup.oreturn (scActive sc) σ) = _
    rw [readSchedContext_eq hk]; rfl
  have : readScReleased (Z := Unit) p σ = some (scReleased σ.curTime x) := by
    show Option.bind (readScActive p σ) (fun a => (if a then readScRefillReady p else Lookup.oreturn false) σ) = _
    rw [ha]
    cases e : scActive x
    · simp [scReleased, e, Lookup.oreturn]
    · simp [scReleased, e, hr]
  simp [getScReleased, NonDet.getsThe, this, NonDet.assertOpt]; rfl

end Spec

theorem sc_released_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) :
    sporadic.sc_released st s sc ⦃ b => Fl4Spec.getScReleased (Z := Unit) sc.bv σ = ({(b, σ)}, False) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  have hne : x.scRefills ≠ [] := by rw [hx.refills]; exact refills_ne hx.wf
  have hact : decide (L.rmax s sc > 0#u64) = Fl4Spec.scActive x := by
    unfold Fl4Spec.scActive Fl4Spec.activeSc
    rw [← hx.max]
    exact decide_eq_decide.2 (by rw [gt_iff_lt, UScalar.lt_equiv]; simp)
  unfold sporadic.sc_released
  refine WP.spec_bind (sc_active_spec s sc) ?_
  rintro b rfl
  rw [getScReleased_eq hk hne]
  by_cases h : L.rmax s sc > 0#u64
  · have hb : decide (L.rmax s sc > 0#u64) = true := decide_eq_true h
    rw [hb]; simp only [↓reduceIte]
    refine WP.spec_mono (ready_refines s σ hS hsc hk) ?_
    intro b hb2
    rw [getScRefillReady_eq hk hne] at hb2
    have e := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb2))).1
    rw [Fl4Spec.scReleased, ← hact, hb, Bool.true_and, e]
  · have hb : decide (L.rmax s sc > 0#u64) = false := decide_eq_false h
    rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [WP.spec_ok, Fl4Spec.scReleased, ← hact, hb, Bool.false_and]

theorem is_blocked_spec (s : S) (t : U64) (ts : Fl4Spec.ThreadState) (hst : (L.mem s (tStA t)).val = tsCode ts) :
    sched.is_blocked st s t ⦃ b => b = Fl4Spec.ipcQueuedThreadState ts ⦄ := by
  unfold sched.is_blocked
  step with Fl4Proofs.P3.Notif.obj.Tcb.state.spec as ⟨v, hv⟩
  subst hv
  have e : ∀ k : U64, (L.mem s (tStA t) = k) ↔ tsCode ts = k.val :=
    fun k => ⟨fun h => h ▸ hst.symm, fun h => UScalar.eq_of_val_eq (hst.trans h)⟩
  have r5 : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
  obtain ⟨-, -, h3, h4, h6⟩ := tsVals
  simp only [e, h3, h4, h6, r5]
  cases ts <;> simp [tsCode, Fl4Spec.ipcQueuedThreadState]


/-- The decoder's restart of the current thread. -/
theorem restart_rels {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hrun : Fl4Spec.runnable xc.tcbState = true) :
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' => ∃ σ',
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ')}, False) ∧
      SRels (st := st) N T C c s' σ' ∧ (∀ q, q ≠ ct.bv → σ'.kheap q = σ.kheap q) ∧
      σ'.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) ∧ σ'.curTime = σ.curTime ∧
      σ'.idleThread = σ.idleThread ∧ σ'.curThread = σ.curThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
      WritesIn st s s' (SFoot st T c s) ⦄ := by
  have hnb : ∀ m, Fl4Spec.ThreadState.restart ≠ .blockedOnNotification m := fun _ h => by cases h
  refine WP.spec_mono (WP.spec_and (set_thread_state_refines s σ hR hS hct hkc (not_in_ntfnQueue hR hct hkc hrun)
    sched.TS_RESTART .restart (by rw [tsVals.2.1]; rfl) hnb) (set_thread_state_sfoot hS hct _)) ?_
  rintro s1 ⟨⟨σ1, he1, hR1, hS1⟩, hwf⟩
  have hσ1 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he1
  refine ⟨σ1, he1, ⟨hS1, hR1, ?_, ?_⟩, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, hwf⟩
  · rw [hσ1]; unfold Fl4Proofs.P3.Notif.stsAct; split <;> exact hN.updTcb
  · rw [hσ1]; exact hI.restart hkc hrun
  · rw [hσ1, stsAct_kheap]; simp [updK, hq]
  · rw [hσ1, stsAct_kheap]; simp [updK]
  all_goals rw [hσ1]; unfold Fl4Proofs.P3.Notif.stsAct; split <;> rfl

/-- **Bind (thread)**: restart, `bind_tcb`. -/
theorem bind_tcb_invoke {N T C : Set U64} {c : U64} (hT : TimeAgree ar) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) (hy0 : y.scTcb = none)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hxt0 : xt.tcbSchedContext = none)
    (hblk : Fl4Spec.runnable xt.tcbState = false → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)
    {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hrun : Fl4Spec.runnable xc.tcbState = true) (call : Bool) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.bind_tcb st ar s2 a sc t
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ res =>
      ScQ (KRels (st := st) N T C c s σ) σ ct call (.invokeSchedContextBind sc.bv (.threadCap t.bv)) res ⦄ := by
  refine WP.spec_bind (restart_rels s σ hS hR hN hI hct hkc hrun) ?_
  rintro s1 ⟨σ1, he1, ⟨hS1, hR1, hN1, hI1⟩, hko1, hkc1, htm1, -, -, -, hw1⟩
  have hz1 : SzKeep σ σ1 := SzKeep.of_tcb hko1 hkc1
  have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
  have hk1 : σ1.kheap sc.bv = some (.schedContext y n) := by rw [hko1 _ hpc]; exact hk
  have key : ∃ xt1, σ1.kheap t.bv = some (.tcb xt1) ∧ xt1.tcbSchedContext = none ∧
      (Fl4Spec.runnable xt1.tcbState = false → inClass xt1.tcbState → Fl4Spec.scActive y = true → released σ1 y) := by
    by_cases e : t = ct
    · subst e; rw [hkc] at hkt; cases hkt
      exact ⟨_, hkc1, hxt0, fun h => by cases h⟩
    · refine ⟨xt, by rw [hko1 _ (bv_ne e)]; exact hkt, hxt0, fun h1 h2 h3 => ?_⟩
      rw [released_congr htm1]; exact hblk h1 h2 h3
  obtain ⟨xt1, hkt1, hxt1, hblk1⟩ := key
  refine WP.spec_bind (bind_tcb_refines s1 a σ1 hS1 hR1 hN1 hI1 hsc hsc0 hk1 hy0 ht hkt1 hxt1 hblk1 hT) ?_
  rintro ⟨s3, a3⟩ ⟨σ3, he3, hS3, hR3, hN3, hI3, -, hw3⟩
  refine (WP.spec_ok _).mpr ⟨rfl, σ1, [], σ3, σ3, he1, ?_, Or.inl ⟨rfl, rfl⟩, ⟨hS3, hR3, hN3, hI3⟩,
    WritesIn.kfoot_trans (WritesIn.kfoot_of_sfoot hw1) (SzKeepC.of hz1) hw3,
    ((pres_setThreadState _ _ _).of_eq he1).trans ((pres_schedContextBindTcb _ _ _).of_eq he3)⟩
  show (Fl4Spec.schedContextBindTcb sc.bv t.bv >>= _) σ1 = _
  rw [nd_bind_one he3]; rfl

/-- **Bind (notification)**: restart, `bind_ntfn`. -/
theorem bind_ntfn_invoke {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) {m : U64} (hm : m ∈ N) (hm0 : m ≠ 0#u64)
    {xm : Fl4Spec.Notification} (hkm : σ.kheap m.bv = some (.notification xm))
    {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hrun : Fl4Spec.runnable xc.tcbState = true) (call : Bool) (b : Fl4Spec.Badge) (r : Fl4Spec.CapRights) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s3 ← schedcontext.bind_ntfn st s2 sc m
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a)) ⦃ res =>
      ScQ (KRels (st := st) N T C c s σ) σ ct call (.invokeSchedContextBind sc.bv (.notificationCap m.bv b r)) res ⦄ := by
  refine WP.spec_bind (restart_rels s σ hS hR hN hI hct hkc hrun) ?_
  rintro s1 ⟨σ1, he1, ⟨hS1, hR1, hN1, hI1⟩, hko1, hkc1, -, -, -, -, hw1⟩
  have hz1 : SzKeep σ σ1 := SzKeep.of_tcb hko1 hkc1
  have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
  have hk1 : σ1.kheap sc.bv = some (.schedContext y n) := by rw [hko1 _ hpc]; exact hk
  have hmc : m.bv ≠ ct.bv := fun e => by rw [e, hkc] at hkm; cases hkm
  have hkm1 : σ1.kheap m.bv = some (.notification xm) := by rw [hko1 _ hmc]; exact hkm
  refine WP.spec_bind (bind_ntfn_refines s1 σ1 hS1 hR1 hN1 hI1 hsc hsc0 hk1 hm hm0 hkm1) ?_
  rintro s3 ⟨σ3, he3, hS3, hR3, hN3, hI3, -, hw3⟩
  refine (WP.spec_ok _).mpr ⟨rfl, σ1, [], σ3, σ3, he1, ?_, Or.inl ⟨rfl, rfl⟩, ⟨hS3, hR3, hN3, hI3⟩,
    WritesIn.kfoot_trans (WritesIn.kfoot_of_sfoot hw1) (SzKeepC.of hz1) hw3,
    ((pres_setThreadState _ _ _).of_eq he1).trans ((pres_schedContextBindNtfn _ _ _).of_eq he3)⟩
  show (Fl4Spec.schedContextBindNtfn sc.bv m.bv >>= _) σ1 = _
  rw [nd_bind_one he3]; rfl

/-- **UnbindObject (thread)**: restart, `unbind_tcb`. -/
theorem unbind_tcb_invoke {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {sc : U64} (hsc : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) {t : U64} (ht : t ∈ T) (hyt : y.scTcb = some t.bv)
    {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hrun : Fl4Spec.runnable xc.tcbState = true) (call : Bool) (cap : Fl4Spec.Cap) (hcap : cap = .threadCap t.bv) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s3 ← schedcontext.unbind_tcb st s2 sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a)) ⦃ res =>
      ScQ (KRels (st := st) N T C c s σ) σ ct call (.invokeSchedContextUnbindObject sc.bv cap) res ⦄ := by
  subst hcap
  refine WP.spec_bind (restart_rels s σ hS hR hN hI hct hkc hrun) ?_
  rintro s1 ⟨σ1, he1, ⟨hS1, hR1, hN1, hI1⟩, hko1, hkc1, -, -, -, -, hw1⟩
  have hz1 : SzKeep σ σ1 := SzKeep.of_tcb hko1 hkc1
  have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
  have hk1 : σ1.kheap sc.bv = some (.schedContext y n) := by rw [hko1 _ hpc]; exact hk
  refine WP.spec_bind (unbind_tcb_refines s1 σ1 hS1 hR1 hN1 hI1 hsc hk1 ht hyt) ?_
  rintro s3 ⟨σ3, he3, hS3, hR3, hN3, hI3, -, hw3, -⟩
  refine (WP.spec_ok _).mpr ⟨rfl, σ1, [], σ3, σ3, he1, ?_, Or.inl ⟨rfl, rfl⟩, ⟨hS3, hR3, hN3, hI3⟩,
    WritesIn.kfoot_trans (WritesIn.kfoot_of_sfoot hw1) (SzKeepC.of hz1)
      (WritesIn.kfoot_of_sfoot_scw hS1 hsc (K := 24#u64) (by simp) (by simp) (by decide) hw3),
    ((pres_setThreadState _ _ _).of_eq he1).trans ((pres_schedContextUnbindTcb _ _).of_eq he3)⟩
  show (Fl4Spec.schedContextUnbindTcb sc.bv >>= _) σ1 = _
  rw [nd_bind_one he3]; rfl

/-- **UnbindObject (notification)**: restart, `unbind_ntfn`. -/
theorem unbind_ntfn_invoke {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) (hbn : ∀ m : U64, y.scNtfn = some m.bv → m ∈ N)
    {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hrun : Fl4Spec.runnable xc.tcbState = true) (call : Bool) (cap : Fl4Spec.Cap)
    (hcap : ∃ p b r, cap = .notificationCap p b r) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s3 ← schedcontext.unbind_ntfn st s2 sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a)) ⦃ res =>
      ScQ (KRels (st := st) N T C c s σ) σ ct call (.invokeSchedContextUnbindObject sc.bv cap) res ⦄ := by
  obtain ⟨p, b, r, rfl⟩ := hcap
  refine WP.spec_bind (restart_rels s σ hS hR hN hI hct hkc hrun) ?_
  rintro s1 ⟨σ1, he1, ⟨hS1, hR1, hN1, hI1⟩, hko1, hkc1, -, -, -, -, hw1⟩
  have hz1 : SzKeep σ σ1 := SzKeep.of_tcb hko1 hkc1
  have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
  have hk1 : σ1.kheap sc.bv = some (.schedContext y n) := by rw [hko1 _ hpc]; exact hk
  refine WP.spec_bind (unbind_ntfn_refines s1 σ1 hS1 hR1 hN1 hI1 hsc hsc0 hk1 hbn) ?_
  rintro s3 ⟨σ3, he3, hS3, hR3, hN3, hI3, -, hw3, -⟩
  refine (WP.spec_ok _).mpr ⟨rfl, σ1, [], σ3, σ3, he1, ?_, Or.inl ⟨rfl, rfl⟩, ⟨hS3, hR3, hN3, hI3⟩,
    WritesIn.kfoot_trans (WritesIn.kfoot_of_sfoot hw1) (SzKeepC.of hz1)
      (WritesIn.kfoot_of_nw_scw hS1 hsc (K := 40#u64) (by simp) (by simp) (by decide) hw3),
    ((pres_setThreadState _ _ _).of_eq he1).trans ((pres_schedContextUnbindNtfn _ _).of_eq he3)⟩
  show (Fl4Spec.schedContextUnbindNtfn sc.bv >>= _) σ1 = _
  rw [nd_bind_one he3]; rfl


theorem decBind_other {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) {a0 : Fl4Spec.Cap}
    (h1 : ∀ t, a0 ≠ .threadCap t) (h2 : ∀ q b r, a0 ≠ .notificationCap q b r) (rest : List Fl4Spec.Cap) :
    (Fl4Spec.decodeSchedContextBind (Z := Unit) p (a0 :: rest)).run σ =
      ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold Fl4Spec.decodeSchedContextBind
  rw [wE_neg (by simp)]
  simp only [Fl4Spec.NonDetE.returnOk, ndE_pure_bind, List.head?_cons, Fl4Spec.the]
  rw [lE_bind (getSchedContext_eq hk)]
  cases a0 <;> first
    | exact absurd rfl (h1 _)
    | exact absurd rfl (h2 _ _ _)
    | (simp only [Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl)

/-- **The Bind label**: no extra cap (truncated), a thread cap (the SC and the
thread unbound, a blocked thread only with a released SC) or a notification
cap (both unbound), anything else invalid; then `bind_tcb_invoke` or
`bind_ntfn_invoke`. -/
theorem bind_branch_refines {N T C : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hcapT : ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ T)
    (hcapN : ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ N ∧ p ≠ 0#u64)
    {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hrun : Fl4Spec.runnable xc.tcbState = true) (call : Bool) :
    ((do
      let o ← schedcontext.extra_cap st s extra 0#usize
      match o with
      | none => let r ← error.truncated Unit
                ok (r, s, a)
      | some c =>
        match c with
        | capability.Cap.Null =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Untyped _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Endpoint _ _ _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Notification ptr _ _ _ =>
          let i1 ← obj.Sc.ntfn st sc s
          if i1 != 0#u64
          then let r ← error.illegal Unit
               ok (r, s, a)
          else
            let i2 ← obj.Ntfn.sc st ptr s
            if i2 != 0#u64
            then let r ← error.illegal Unit
                 ok (r, s, a)
            else
              let s2 ←
                sched.set_thread_state st s ct sched.TS_RESTART
              let s3 ← schedcontext.bind_ntfn st s2 sc ptr
              ok (core.result.Result.Ok (), s3, a)
        | capability.Cap.Reply _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.CNode _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Thread ptr =>
          let i1 ← obj.Sc.tcb st sc s
          if i1 != 0#u64
          then let r ← error.illegal Unit
               ok (r, s, a)
          else
            let i2 ← obj.Tcb.sc st ptr s
            if i2 != 0#u64
            then let r ← error.illegal Unit
                 ok (r, s, a)
            else
              let b ← sched.is_blocked st s ptr
              if b
              then
                let b1 ← sporadic.sc_released st s sc
                if b1
                then
                  let s2 ←
                    sched.set_thread_state st s ct
                      sched.TS_RESTART
                  let (s3, a2) ←
                    schedcontext.bind_tcb st ar s2
                      a sc ptr
                  ok (core.result.Result.Ok (), s3, a2)
                else let r ← error.illegal Unit
                     ok (r, s, a)
              else
                let s2 ←
                  sched.set_thread_state st s ct
                    sched.TS_RESTART
                let (s3, a2) ←
                  schedcontext.bind_tcb st ar s2 a
                    sc ptr
                ok (core.result.Result.Ok (), s3, a2)
        | capability.Cap.IrqControl =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.IrqHandler _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Zombie _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Domain =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.SchedContext _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.SchedControl _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Frame _ _ _ _ _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.PageTable _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.PageDirectory _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Pdpt _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Pml4 _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Vcpu _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Ept _ _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.AsidControl =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.AsidPool _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.IoPortControl =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.IoPort _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)) : Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
      CPost σ (Fl4Spec.decodeSchedContextBind (Z := Unit) sc.bv excaps) s a
        (ScQ (KRels (st := st) N T C c s σ) σ ct call) res ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨y, n, hk, hx⟩ := hs.scs sc hsc
  unfold schedcontext.extra_cap
  have h03 : ¬ (0#usize ≥ 3#usize) := by decide
  simp only [h03, ↓reduceIte, hx0, bind_ok, obj.Slot.is_null]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, c0, a0, rest0, hc0, hca0, hcv0, rfl⟩
  · simp only [decide_true, ↓reduceIte, bind_ok, error.truncated]
    apply CPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) _ (Or.inl trivial)
    unfold Fl4Spec.decodeSchedContextBind
    exact wE_pos (by simp) _ _ σ
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, hc0, bind_ok]
  obtain ⟨hwf, rfl⟩ := hca0
  have hpre : ∀ (cap : Fl4Spec.Cap), (Fl4Spec.decodeSchedContextBind (Z := Unit) sc.bv (cap :: rest0)).run σ =
      ((match cap with
        | .threadCap tcbPtr => do
          Fl4Spec.NonDetE.whenE (y.scTcb ≠ none) <| Fl4Spec.NonDetE.throwError .illegalOperation
          let scPtrOpt ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext tcbPtr
          Fl4Spec.NonDetE.whenE (scPtrOpt ≠ none) <| Fl4Spec.NonDetE.throwError .illegalOperation
          let st ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getThreadState (Z := Unit) tcbPtr
          let released ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getScReleased (Z := Unit) sc.bv
          Fl4Spec.NonDetE.whenE (Fl4Spec.ipcQueuedThreadState st ∧ ¬released) <|
            Fl4Spec.NonDetE.throwError .illegalOperation
          Fl4Spec.NonDetE.returnOk <| .invokeSchedContextBind sc.bv cap
        | .notificationCap ntfnPtr _ _ => do
          Fl4Spec.NonDetE.whenE (y.scNtfn ≠ none) <| Fl4Spec.NonDetE.throwError .illegalOperation
          let scPtrOpt ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getNtfnObjRef (Z := Unit) Fl4Spec.Notification.ntfnSc ntfnPtr
          Fl4Spec.NonDetE.whenE (scPtrOpt ≠ none) <| Fl4Spec.NonDetE.throwError .illegalOperation
          Fl4Spec.NonDetE.returnOk <| .invokeSchedContextBind sc.bv cap
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation)).run σ := by
    intro cap
    unfold Fl4Spec.decodeSchedContextBind
    rw [wE_neg (by simp)]
    simp only [Fl4Spec.NonDetE.returnOk, ndE_pure_bind, List.head?_cons, Fl4Spec.the]
    rw [lE_bind (getSchedContext_eq hk)]
    cases cap <;> simp only [Fl4Spec.NonDetE.throwError, ndE_throw_bind] <;> rfl
  have hxt' : y.scTcb = optRef (L.mem s (scW sc 24#u64)) := hx.tcb
  have hxn' : y.scNtfn = optRef (L.mem s (scW sc 40#u64)) := hx.ntfn
  have hill : ∀ (P : Prop) [Decidable P], P → ∀ f : Unit → Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation,
      (Fl4Spec.NonDetE.whenE P (Fl4Spec.NonDetE.throwError .illegalOperation) >>= f).run σ =
        ({(.error .illegalOperation, σ)}, False) := fun P _ h f => wE_pos h _ f σ
  cases c0
  case Thread ptr =>
    have hpT := hcapT ptr hc0
    obtain ⟨xt, hkt, -, -, hxts, -⟩ := hs.tcb ptr hpT
    have hst := (hR.at_tcb hpT hkt).st
    step with obj.Sc.tcb.spec as ⟨i1, hi1⟩
    rw [scTcbA_eq] at hi1
    subst hi1
    by_cases h1 : L.mem s (scW sc 24#u64) = 0#u64
    swap
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = true := by simp [h1]
      simp only [this, ↓reduceIte]
      refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
      rw [hpre]; simp only [absCap]
      exact hill _ (by rw [hxt', optRef_ne h1]; simp) _
    have : (L.mem s (scW sc 24#u64) != 0#u64) = false := by simp [h1]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    have hy0 : y.scTcb = none := by rw [hxt', h1, optRef_zero]
    step with obj.Tcb.sc.spec as ⟨i2, hi2⟩
    subst hi2
    have hpre2 := hpre (.threadCap ptr.bv)
    simp only [absCap] at hpre2 ⊢
    rw [wE_neg (by simp [hy0]), lE_bind (Fl4Proofs.P3.Endp.getTcbObjRef_eq _ hkt)] at hpre2
    by_cases h2 : L.mem s (scA ptr) = 0#u64
    swap
    · have : (L.mem s (scA ptr) != 0#u64) = true := by simp [h2]
      simp only [this, ↓reduceIte]
      refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
      rw [hpre2]
      exact hill _ (by rw [hxts, optRef_ne h2]; simp) _
    have : (L.mem s (scA ptr) != 0#u64) = false := by simp [h2]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    have hxt0 : xt.tcbSchedContext = none := by rw [hxts, h2, optRef_zero]
    have hne : y.scRefills ≠ [] := by rw [hx.refills]; exact refills_ne hx.wf
    rw [wE_neg (by simp [hxt0]), lE_bind (getThreadState_eq hkt), lE_bind (getScReleased_eq hk hne)] at hpre2
    refine WP.spec_bind (is_blocked_spec s ptr xt.tcbState hst) ?_
    rintro b rfl
    have hinv := bind_tcb_invoke (st := st) (ar := ar) hT s a σ hS hR hN hI hsc hsc0 hk hy0 hpT hkt hxt0
    by_cases hb : Fl4Spec.ipcQueuedThreadState xt.tcbState = true
    · simp only [hb, ↓reduceIte]
      refine WP.spec_bind (sc_released_refines s σ hS hsc hk) ?_
      intro b1 hb1
      rw [getScReleased_eq hk hne] at hb1
      have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
      by_cases hr : b1 = true
      · simp only [hr, ↓reduceIte]
        have hrel : Fl4Spec.scReleased σ.curTime y = true := eb.trans hr
        have hblk : Fl4Spec.runnable xt.tcbState = false → inClass xt.tcbState → Fl4Spec.scActive y = true →
            released σ y := by
          intro _ _ ha
          simp only [Fl4Spec.scReleased, Bool.and_eq_true] at hrel
          exact ⟨hrel.2, hI.suff hk ha⟩
        refine WP.spec_mono (hinv hblk hct hkc hrun call) fun r hr' => Or.inr ⟨_, ?_, hr'⟩
        rw [hpre2, wE_neg (by simp [hrel])]; rfl
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
        rw [hpre2]
        exact hill _ ⟨hb, by rw [eb]; simpa using hr⟩ _
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hblk : Fl4Spec.runnable xt.tcbState = false → inClass xt.tcbState → Fl4Spec.scActive y = true →
          released σ y := by
        intro h1' h2' _
        rcases h2' with h | ⟨m, h⟩
        · rw [h] at h1'; cases h1'
        · rw [h] at hb; exact absurd rfl hb
      refine WP.spec_mono (hinv hblk hct hkc hrun call) fun r hr' => Or.inr ⟨_, ?_, hr'⟩
      rw [hpre2, wE_neg (by simp [hb])]; rfl
  case Notification ptr bb ww rr =>
    obtain ⟨hpN, hp0⟩ := hcapN ptr bb ww rr hc0
    obtain ⟨xm, hkm, hxm⟩ := hR.ntfn ptr hpN
    step with obj.Sc.ntfn.spec2 as ⟨i1, hi1⟩
    subst hi1
    have hpre2 := hpre (absCap (.Notification ptr bb ww rr))
    simp only [absCap] at hpre2 ⊢
    by_cases h1 : L.mem s (scW sc 40#u64) = 0#u64
    swap
    · have : (L.mem s (scW sc 40#u64) != 0#u64) = true := by simp [h1]
      simp only [this, ↓reduceIte]
      refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
      rw [hpre2]
      exact hill _ (by rw [hxn', optRef_ne h1]; simp) _
    have : (L.mem s (scW sc 40#u64) != 0#u64) = false := by simp [h1]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    rw [wE_neg (by simp [hxn', h1, optRef_zero]), lE_bind (getNtfnSc_eq hkm)] at hpre2
    step with obj.Ntfn.sc.spec as ⟨i2, hi2⟩
    subst hi2
    by_cases h2 : L.mem s (nScA ptr) = 0#u64
    swap
    · have : (L.mem s (nScA ptr) != 0#u64) = true := by simp [h2]
      simp only [this, ↓reduceIte]
      refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
      rw [hpre2]
      exact hill _ (by rw [hxm.sc, optRef_ne h2]; simp) _
    have : (L.mem s (nScA ptr) != 0#u64) = false := by simp [h2]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (bind_ntfn_invoke s a σ hS hR hN hI hsc hsc0 hk hpN hp0 hkm hct hkc hrun call bb.bv
      (rightsOf ww rr false false))
      fun r hr' => Or.inr ⟨_, ?_, hr'⟩
    rw [hpre2, wE_neg (by simp [hxm.sc, h2, optRef_zero])]; rfl
  all_goals
    simp only [error.invalid_cap, bind_ok]
    exact CPost.err (decBind_other hk (by simp [absCap]) (by simp [absCap]) rest0) (Or.inr ⟨1#u64, rfl, rfl⟩)


theorem bv_optRef_some {i p : U64} (hp : p ≠ 0#u64) : optRef i = some p.bv ↔ i = p := by
  constructor
  · intro h
    by_cases hi : i = 0#u64
    · rw [hi, optRef_zero] at h; cases h
    · rw [optRef_ne hi] at h; exact eq_of_bv (Option.some.inj h)
  · rintro rfl; exact optRef_ne hp

/-- **The UnbindObject label**: no extra cap (truncated), the SC's thread
(not the caller) or the SC's notification, anything else invalid; then
`unbind_tcb_invoke` or `unbind_ntfn_invoke`. -/
theorem unbindobj_branch_refines {N T C : Set U64} {c : U64} (th : TypedHeap)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hcapT : ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ T)
    (hcapN : ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ N ∧ p ≠ 0#u64)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xc : Fl4Spec.Tcb}
    (hkc : σ.kheap ct.bv = some (.tcb xc)) (hrun : Fl4Spec.runnable xc.tcbState = true) (call : Bool) :
    ((do
      let o ← schedcontext.extra_cap st s extra 0#usize
      match o with
      | none => let r ← error.truncated Unit
                ok (r, s, a)
      | some c =>
        match c with
        | capability.Cap.Null =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Untyped _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Endpoint _ _ _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Notification ptr _ _ _ =>
          let i1 ← obj.Sc.ntfn st sc s
          if i1 != ptr
          then let r ← error.illegal Unit
               ok (r, s, a)
          else
            let s2 ←
              sched.set_thread_state st s ct sched.TS_RESTART
            let s3 ← schedcontext.unbind_ntfn st s2 sc
            ok (core.result.Result.Ok (), s3, a)
        | capability.Cap.Reply _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.CNode _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Thread ptr =>
          let i1 ← obj.Sc.tcb st sc s
          if i1 != ptr
          then let r ← error.illegal Unit
               ok (r, s, a)
          else
            if ptr = ct
            then let r ← error.illegal Unit
                 ok (r, s, a)
            else
              let s2 ←
                sched.set_thread_state st s ct
                  sched.TS_RESTART
              let s3 ← schedcontext.unbind_tcb st s2 sc
              ok (core.result.Result.Ok (), s3, a)
        | capability.Cap.IrqControl =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.IrqHandler _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Zombie _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Domain =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.SchedContext _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.SchedControl _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Frame _ _ _ _ _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.PageTable _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.PageDirectory _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Pdpt _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Pml4 _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Vcpu _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.Ept _ _ _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.AsidControl =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.AsidPool _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.IoPortControl =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)
        | capability.Cap.IoPort _ _ _ =>
          let r ← error.invalid_cap Unit 1#u64
          ok (r, s, a)) : Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
      CPost σ (Fl4Spec.decodeSchedContextUnbindObject (Z := Unit) sc.bv excaps) s a
        (ScQ (KRels (st := st) N T C c s σ) σ ct call) res ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨y, n, hk, hx⟩ := hs.scs sc hsc
  unfold schedcontext.extra_cap
  have h03 : ¬ (0#usize ≥ 3#usize) := by decide
  simp only [h03, ↓reduceIte, hx0, bind_ok, obj.Slot.is_null]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, c0, a0, rest0, hc0, hca0, hcv0, rfl⟩
  · simp only [decide_true, ↓reduceIte, bind_ok, error.truncated]
    apply CPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) _ (Or.inl trivial)
    unfold Fl4Spec.decodeSchedContextUnbindObject
    exact wE_pos (by simp) _ _ σ
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, hc0, bind_ok]
  obtain ⟨hwf, rfl⟩ := hca0
  have hpre : ∀ (cap : Fl4Spec.Cap), (Fl4Spec.decodeSchedContextUnbindObject (Z := Unit) sc.bv (cap :: rest0)).run σ =
      ((match cap with
        | .threadCap tcbPtr => do
          let scTcbOpt ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scTcb sc.bv
          Fl4Spec.NonDetE.whenE (scTcbOpt ≠ some tcbPtr) <| Fl4Spec.NonDetE.throwError .illegalOperation
          let ctPtr ← Fl4Spec.NonDetE.liftE <| Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
          Fl4Spec.NonDetE.whenE (tcbPtr = ctPtr) <| Fl4Spec.NonDetE.throwError .illegalOperation
          Fl4Spec.NonDetE.returnOk <| .invokeSchedContextUnbindObject sc.bv cap
        | .notificationCap ntfnPtr _ _ => do
          let scNtfnOpt ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scNtfn sc.bv
          Fl4Spec.NonDetE.whenE (scNtfnOpt ≠ some ntfnPtr) <| Fl4Spec.NonDetE.throwError .illegalOperation
          Fl4Spec.NonDetE.returnOk <| .invokeSchedContextUnbindObject sc.bv cap
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation)).run σ := by
    intro cap
    unfold Fl4Spec.decodeSchedContextUnbindObject
    rw [wE_neg (by simp)]
    simp only [Fl4Spec.NonDetE.returnOk, ndE_pure_bind, List.head?_cons, Fl4Spec.the]
    cases cap <;> simp only [Fl4Spec.NonDetE.throwError, ndE_throw_bind] <;> rfl
  have hxt' : y.scTcb = optRef (L.mem s (scW sc 24#u64)) := hx.tcb
  have hxn' : y.scNtfn = optRef (L.mem s (scW sc 40#u64)) := hx.ntfn
  have hill : ∀ (P : Prop) [Decidable P], P → ∀ f : Unit → Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation,
      (Fl4Spec.NonDetE.whenE P (Fl4Spec.NonDetE.throwError .illegalOperation) >>= f).run σ =
        ({(.error .illegalOperation, σ)}, False) := fun P _ h f => wE_pos h _ f σ
  cases c0
  case Thread ptr =>
    have hpT := hcapT ptr hc0
    have hp0 : ptr ≠ 0#u64 := fun e => (hc.tcbs ptr hpT).ne0 (by rw [e]; rfl)
    have hpre2 := hpre (.threadCap ptr.bv)
    simp only [absCap] at hpre2 ⊢
    rw [lE_bind (getScObjRef_eq hk _)] at hpre2
    step with obj.Sc.tcb.spec as ⟨i1, hi1⟩
    rw [scTcbA_eq] at hi1
    subst hi1
    by_cases h1 : L.mem s (scW sc 24#u64) = ptr
    swap
    · have : (L.mem s (scW sc 24#u64) != ptr) = true := by simp [h1]
      simp only [this, ↓reduceIte]
      refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
      rw [hpre2]
      exact hill _ (by rw [hxt']; exact fun h => h1 ((bv_optRef_some hp0).1 h)) _
    have : (L.mem s (scW sc 24#u64) != ptr) = false := by simp [h1]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    have hyt : y.scTcb = some ptr.bv := by rw [hxt', (bv_optRef_some hp0).2 h1]
    rw [wE_neg (by simp [hyt]), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
      ({(σ.curThread, σ)}, False) from rfl), hcur] at hpre2
    by_cases h2 : ptr = ct
    · rw [ite_eq_left h2]
      refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
      rw [hpre2]
      exact hill _ (by rw [h2]) _
    rw [ite_eq_right h2]
    refine WP.spec_mono (unbind_tcb_invoke s a σ hS hR hN hI hsc hk hpT hyt hct hkc hrun call _ rfl)
      fun r hr' => Or.inr ⟨_, ?_, hr'⟩
    rw [hpre2, wE_neg (fun h => h2 (eq_of_bv h))]; rfl
  case Notification ptr bb ww rr =>
    obtain ⟨hpN, hp0⟩ := hcapN ptr bb ww rr hc0
    have hpre2 := hpre (absCap (.Notification ptr bb ww rr))
    simp only [absCap] at hpre2 ⊢
    rw [lE_bind (getScObjRef_eq hk _)] at hpre2
    step with obj.Sc.ntfn.spec2 as ⟨i1, hi1⟩
    subst hi1
    by_cases h1 : L.mem s (scW sc 40#u64) = ptr
    swap
    · have : (L.mem s (scW sc 40#u64) != ptr) = true := by simp [h1]
      simp only [this, ↓reduceIte]
      refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
      rw [hpre2]
      exact hill _ (by rw [hxn']; exact fun h => h1 ((bv_optRef_some hp0).1 h)) _
    have : (L.mem s (scW sc 40#u64) != ptr) = false := by simp [h1]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    have hyn : y.scNtfn = some ptr.bv := by rw [hxn', (bv_optRef_some hp0).2 h1]
    refine WP.spec_mono (unbind_ntfn_invoke s a σ hS hR hN hI hsc hsc0 hk
      (fun m hm => by rw [hyn] at hm; rw [eq_of_bv (Option.some.inj hm).symm]; exact hpN) hct hkc hrun call
      (.notificationCap ptr.bv bb.bv (rightsOf ww rr false false)) ⟨_, _, _, rfl⟩) fun r hr' => Or.inr ⟨_, ?_, hr'⟩
    rw [hpre2, wE_neg (by simp [hyn])]; rfl
  all_goals
    simp only [error.invalid_cap, bind_ok]
    refine CPost.err ?_ (Or.inr ⟨1#u64, rfl, rfl⟩)
    rw [hpre]; simp only [absCap, Fl4Spec.NonDetE.throwError]; rfl


/-- The spec's label of FL4's SchedContext label. -/
def scLabelOf (lbl : U64) : Fl4Spec.GenInvocationLabels :=
  if lbl.val = 41 then .schedContextBind else if lbl.val = 42 then .schedContextUnbind
  else if lbl.val = 43 then .schedContextUnbindObject else if lbl.val = 44 then .schedContextConsumed
  else if lbl.val = 45 then .schedContextYieldTo else .invalidInvocation

@[simp] theorem lbl_scbind_val : fl4_abi.label.SchedContextBind.val = 41 := by simp [fl4_abi.label.SchedContextBind]
@[simp] theorem lbl_scunbind_val : fl4_abi.label.SchedContextUnbind.val = 42 := by
  simp [fl4_abi.label.SchedContextUnbind]
@[simp] theorem lbl_scunbindobj_val : fl4_abi.label.SchedContextUnbindObject.val = 43 := by
  simp [fl4_abi.label.SchedContextUnbindObject]
@[simp] theorem lbl_scconsumed_val : fl4_abi.label.SchedContextConsumed.val = 44 := by
  simp [fl4_abi.label.SchedContextConsumed]
@[simp] theorem lbl_scyield_val : fl4_abi.label.SchedContextYieldTo.val = 45 := by
  simp [fl4_abi.label.SchedContextYieldTo]

theorem CPost.congr {α : Type} {σ : Fl4Spec.State Unit} {m m' : Fl4Spec.SEMonad Unit α} {s : S} {a : A} {Q}
    {res : core.result.Result Unit error.Exc × S × A} (h : m.run σ = m'.run σ) (hc : CPost σ m' s a Q res) :
    CPost σ m s a Q res := by
  unfold CPost at hc ⊢; rw [h]; exact hc

theorem CPost.mono {α : Type} {σ : Fl4Spec.State Unit} {m : Fl4Spec.SEMonad Unit α} {s : S} {a : A} {Q Q'}
    {res : core.result.Result Unit error.Exc × S × A} (hc : CPost σ m s a Q res) (hq : ∀ i r, Q i r → Q' i r) :
    CPost σ m s a Q' res := by
  rcases hc with h | ⟨i, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, h1, hq i res h2⟩

theorem ScQ.mono {R1 R2 : S → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {ct : U64} {call : Bool}
    {inv : Fl4Spec.SchedContextInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (h : ScQ (A := A) R1 σ ct call inv res) (hr : ∀ s σ', R1 s σ' → R2 s σ') : ScQ R2 σ ct call inv res := by
  obtain ⟨h1, σ0, data, σ1, σ2, e0, e1, e2, e3⟩ := h
  exact ⟨h1, σ0, data, σ1, σ2, e0, e1, e2, hr _ _ e3⟩

end

end

end Fl4Proofs.P3.Sched
