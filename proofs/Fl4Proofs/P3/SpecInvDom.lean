/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, invC): **`DomListOK` is
kept by the spec's kernel entry** (spec side only, outside the JAtZ cone).

* `DomListOK` (ScNextDom: l4v `valid_domain_list` and FL4's one domain) reads
  only `dlV` (SpecInvDomF), so every `DL` frame keeps it (`domListOK_of_dlV`).
* `DP m`: every outcome of `m` from a `DomListOK` state is `DomListOK`; its
  combinators and `dp_auto` (structural steps, then a `DL` frame by
  `dl_auto` for a whole leaf).
* The three writers: `next_domain` (`dp_nextDomain`: the index never reaches
  the final end marker, since the start entry is no end marker),
  `domain_set_start` and `domain_schedule_configure` (`dp_invokeDomain`, from
  `DomInvOK`: the checks of `decode_domain_schedule_set_start` /
  `decode_domain_schedule_configure`, l4v
  `domain_set_start_valid_domain_list_inv` /
  `domain_schedule_configure_valid_domain_list`). The configured entry's domain
  is 0 by the decode's `domain < numDomains` check and `numDomains = 1` [P]
  (FL4's one-domain configuration, `JEntryGlob.nd` / `hnd`): the one hypothesis.
* `okd_fl4Decode`: every decoded invocation satisfies `DomInvOK` at the
  decode's end state; `dpe_handleInvocationR`: the invocation shell (copy of
  sch12's `syscall_post`, XTopJointMidRunS, which is inside the JAtZ cone),
  `DomInvOK` carried from the decode across `set_thread_state Restart` by the
  frame.
* Tops: `kentry_domListOK` (syscall entry, `fl4KernelEntrySyscall`),
  `kcall_domListOK` (`fl4CallKernel rep ev`, every event: the interrupt and
  timer entries go through it with `ev = .interrupt`; Fl4Spec has no separate
  interrupt entry), `domListOK_init` (Fl4Spec's `initASt`).
-/
import Fl4Proofs.P3.SpecInvDomE
import Fl4Proofs.P3.ScNextDom
import Fl4Spec.Init
open Classical

namespace Fl4Proofs.P3.SInvDom
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

theorem domListOK_of_dlV {σ σ' : State Unit} (e : dlV σ' = dlV σ) (h : DomListOK σ) : DomListOK σ' := by
  simp only [dlV, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  exact ⟨by rw [e1]; exact h.len, by rw [e1]; exact h.zero, by rw [e1, e2]; exact h.start,
    by rw [e1, e2]; exact h.startNE, by rw [e1]; exact h.last, by rw [e1, e3]; exact h.idx,
    by rw [e1]; exact h.dom⟩

/-! ## `DP`: `DomListOK` kept -/

/-- Every outcome of `m` from a `DomListOK` state is `DomListOK`. -/
def DP {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, DomListOK σ → x ∈ (m σ).1 → DomListOK x.2

abbrev DPE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := DP (ExceptT.run m)

section Comb

theorem dp_of_dl {α : Type} {m : NonDet (State Unit) α} (h : DL m) : DP m :=
  fun σ x hs hx => domListOK_of_dlV (h σ x hx) hs

theorem dpe_of_dle {ε α : Type} {m : NonDetE (State Unit) ε α} (h : DLE m) : DPE m := dp_of_dl h

theorem dp_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : DP m)
    (hg : ∀ a, DP (g a)) : DP (m >>= g) := by
  intro σ x hs ⟨y, hy, hx⟩
  exact hg y.1 y.2 x (hm σ y hs hy) hx

theorem dp_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : DP m)
    (hg : ∀ a, DP (g a)) : DP (NonDet.bind m g) := dp_bind hm hg

theorem dp_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : DP m1)
    (h2 : DP m2) : DP (if P then m1 else m2) := by
  split <;> assumption

theorem dp_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : DP m) :
    DP (NonDet.when P m) := by
  unfold NonDet.when; exact dp_ite P h (dp_of_dl (dk_pure' _))

theorem dpe_bind {ε α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ}
    (hm : DPE m) (hg : ∀ a, DPE (g a)) : DPE (m >>= g) := by
  show DP (ExceptT.run (m >>= g))
  rw [ExceptT.run_bind]
  refine dp_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact dp_of_dl (dk_pure _)

theorem dpe_liftE {ε α : Type} {m : NonDet (State Unit) α} (h : DP m) : DPE (NonDetE.liftE (ε := ε) m) := by
  show DP (ExceptT.run (NonDetE.liftE m))
  unfold NonDetE.liftE; rw [ExceptT.run_lift]
  exact dp_bind h fun _ => dp_of_dl (dk_pure _)

theorem dpe_ite {ε α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : DPE m1)
    (h2 : DPE m2) : DPE (if P then m1 else m2) := by
  split <;> assumption

theorem dpe_whenE {ε : Type} (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : DPE m) :
    DPE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact dpe_ite P h (dpe_of_dle (dke_pure _))

theorem dpe_handleE {ε ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : DPE m) (hh : ∀ e, DPE (h e)) : DPE (NonDetE.handleE m h) := by
  show DP (ExceptT.run (NonDetE.handleE m h))
  unfold NonDetE.handleE
  rw [ExceptT.run_mk]
  refine dp_bind' hm fun r => ?_
  cases r with
  | ok a => exact dp_of_dl (dk_pure' _)
  | error e => exact hh e

end Comb

/-- A `DP` lemma of a spec function (extended below, one rule per lemma). -/
syntax "dp_leaf" : tactic
macro_rules | `(tactic| dp_leaf) => `(tactic| fail "no dp_leaf")

macro "dp_step" : tactic => `(tactic| first
  | dp_leaf
  | (with_reducible refine dp_bind ?_ (fun _ => ?_))
  | (with_reducible refine dp_bind' ?_ (fun _ => ?_))
  | (with_reducible refine dpe_bind ?_ (fun _ => ?_))
  | (with_reducible apply dp_ite) | (with_reducible apply dp_when)
  | (with_reducible apply dpe_ite) | (with_reducible apply dpe_whenE) | (with_reducible apply dpe_liftE)
  | (with_reducible refine dpe_handleE ?_ (fun _ => ?_))
  | split
  | (apply dp_of_dl; (dl_auto; done))
  | (apply dpe_of_dle; (dl_auto; done)))

macro "dp_auto" : tactic => `(tactic| repeat' dp_step)

/-! ## The scheduler: `next_domain` -/

/-- **`next_domain` keeps `DomListOK`**: the new index is the start (below
the final end marker, the start entry being none) or the old index plus one,
which is not the final end marker's. -/
theorem dp_nextDomain : DP (nextDomain (Z := Unit)) := by
  unfold nextDomain
  refine dp_bind ?_ fun _ => dp_of_dl (dl_doExtendedOp _)
  intro σ x hs hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  refine ⟨hs.len, hs.zero, hs.start, hs.startNE, hs.last, ?_, hs.dom⟩
  dsimp only
  split
  · have h1 := hs.start
    have h2 := hs.startNE
    have h3 := hs.last
    refine Nat.lt_of_le_of_ne (by omega) fun hc => h2 ?_
    rw [hc]; exact h3
  · rename_i hne
    have h1 := hs.idx
    refine Nat.lt_of_le_of_ne (by omega) fun e => hne ?_
    rw [e, hs.last]; rfl
macro_rules | `(tactic| dp_leaf) => `(tactic| with_reducible exact dp_nextDomain)

set_option maxHeartbeats 4000000 in
theorem dp_scheduleChooseNewThread : DP (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; dp_auto
macro_rules | `(tactic| dp_leaf) => `(tactic| with_reducible exact dp_scheduleChooseNewThread)

set_option maxHeartbeats 4000000 in
/-- **`schedule` keeps `DomListOK`.** -/
theorem dp_schedule : DP (schedule (Z := Unit)) := by
  unfold schedule; dp_auto
macro_rules | `(tactic| dp_leaf) => `(tactic| with_reducible exact dp_schedule)

/-! ## The Domain invocations -/

/-- **What the decode checks for the domain-schedule invocations**, at the
state of the perform (it reads only the domain list and its start). -/
def DomInvOK (σ : State Unit) : Fl4Invocation → Prop
  | .invokeDomain (.invokeDomainScheduleSetStart i) =>
    i < σ.domainList.length ∧ σ.domainList[i]? ≠ some domainEndMarker
  | .invokeDomain (.invokeDomainScheduleConfigure i d dur) =>
    i < σ.domainList.length - 1 ∧ d = 0 ∧ (i = σ.domainStartIndex → dur ≠ 0)
  | _ => True

theorem domInvOK_of_dlV {σ σ' : State Unit} (e : dlV σ' = dlV σ) {inv : Fl4Invocation}
    (h : DomInvOK σ inv) : DomInvOK σ' inv := by
  simp only [dlV, Prod.mk.injEq] at e
  obtain ⟨e1, e2, -⟩ := e
  cases inv with
  | invokeDomain d =>
    cases d with
    | invokeDomainSet => trivial
    | invokeDomainScheduleSetStart i => simp only [DomInvOK, e1] at h ⊢; exact h
    | invokeDomainScheduleConfigure i d dur => simp only [DomInvOK, e1, e2] at h ⊢; exact h
  | _ => trivial

theorem dp_domainSetStart (i : Nat) (σ : State Unit) (x : Unit × State Unit) (hs : DomListOK σ)
    (hi : i < σ.domainList.length) (hne : σ.domainList[i]? ≠ some domainEndMarker)
    (hx : x ∈ (domainSetStart (Z := Unit) i σ).1) : DomListOK x.2 := by
  unfold domainSetStart at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy1
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy2
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy3
  obtain ⟨y4, hy4, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy4
  refine domListOK_of_dlV (dl_rescheduleRequired _ x hx) ?_
  have hl := hs.len
  exact ⟨hs.len, hs.zero, hi, hne, hs.last, by dsimp only; omega, hs.dom⟩

theorem dp_domainScheduleConfigure (i : Nat) (d : Domain) (dur : DomainDuration) (σ : State Unit)
    (x : Unit × State Unit) (hs : DomListOK σ) (hi : i < σ.domainList.length - 1) (hd : d = 0)
    (hst : i = σ.domainStartIndex → dur ≠ 0)
    (hx : x ∈ (domainScheduleConfigure (Z := Unit) i d dur σ).1) : DomListOK x.2 := by
  unfold domainScheduleConfigure at hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  subst hd
  have hl := hs.len
  have hmem : ∀ e ∈ σ.domainList.set i ((0 : Domain), dur), e = ((0 : Domain), dur) ∨ e ∈ σ.domainList :=
    fun e he => (List.mem_or_eq_of_mem_set he).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [List.length_set]; exact hs.len
  · intro e he _
    rcases hmem e he with rfl | h
    · rfl
    · exact hs.zero e h ‹_›
  · rw [List.length_set]; exact hs.start
  · rw [List.getElem?_set]
    by_cases h : i = σ.domainStartIndex
    · subst h
      rw [if_pos rfl, if_pos (by omega)]
      intro e
      have := hst rfl
      simp only [Option.some.injEq, domainEndMarker, Prod.mk.injEq] at e
      exact this e.2
    · rw [if_neg h]; exact hs.startNE
  · rw [List.length_set, List.getElem?_set, if_neg (by omega)]; exact hs.last
  · rw [List.length_set]; exact hs.idx
  · intro e he
    rcases hmem e he with rfl | h
    · rfl
    · exact hs.dom e h

set_option maxHeartbeats 4000000 in
theorem dl_invokeSetDomain (t : ObjRef) (d : Domain) : DL (invokeSetDomain (Z := Unit) t d) := by
  dl_auto

/-- **The Domain invocations keep `DomListOK`**, from `DomInvOK`. -/
theorem dp_invokeDomain (di : DomainInvocation) (σ : State Unit) (x : Unit × State Unit) (hs : DomListOK σ)
    (hi : DomInvOK σ (.invokeDomain di)) (hx : x ∈ (invokeDomain (Z := Unit) di σ).1) : DomListOK x.2 := by
  cases di with
  | invokeDomainSet t d => exact dp_of_dl (dl_invokeSetDomain t d) σ x hs hx
  | invokeDomainScheduleSetStart i => exact dp_domainSetStart i σ x hs hi.1 hi.2 hx
  | invokeDomainScheduleConfigure i d dur => exact dp_domainScheduleConfigure i d dur σ x hs hi.1 hi.2.1 hi.2.2 hx

/-! ## The decode's checks -/

theorem mem_bindE_inv' {σ ε α β : Type} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ}
    {x : Except ε β × σ} (hx : x ∈ ((m >>= f).run s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ x ∈ ((f a).run z.2).1) ∨ (∃ e, z.1 = .error e ∧ x = (.error e, z.2)) := by
  rw [ExceptT.run_bind] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact Or.inl ⟨a, rfl, hxz⟩
  | error e => exact Or.inr ⟨e, rfl, Set.mem_singleton_iff.1 hxz⟩

theorem mem_liftE_inv' {σ ε α : Type} {m : NonDet σ α} {s : σ} {y : Except ε α × σ}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y = (.ok x.1, x.2) := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hx, Set.mem_singleton_iff.1 hy⟩

/-- Every `.ok` outcome of `m` from `σ` satisfies `P` at its state. -/
def OkDAt {ε α : Type} (σ : State Unit) (P : State Unit → α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → P s a

section OkD
variable {ε α β : Type} {σ : State Unit}

theorem okdAt_bind {P : State Unit → β → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hg : ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → OkDAt s P (g a)) :
    OkDAt σ P (m >>= g) := by
  intro b s hb
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := mem_bindE_inv' hb
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    exact hg a s' hz b s hy
  · simp at he

theorem okdAt_returnOk {P : State Unit → α → Prop} {v : α} (h : P σ v) :
    OkDAt σ P (NonDetE.returnOk v : NonDetE (State Unit) ε α) := by
  intro a s h'
  have e := Set.mem_singleton_iff.1 h'
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact h

theorem okdAt_throw {P : State Unit → α → Prop} (e : ε) :
    OkDAt σ P (NonDetE.throwError e : NonDetE (State Unit) ε α) := by
  intro a s h'
  have e := Set.mem_singleton_iff.1 h'
  simp at e

theorem okdAt_whenE_bind {P : State Unit → β → Prop} (c : Prop) [Decidable c] (e : ε)
    {g : Unit → NonDetE (State Unit) ε β} (hg : ¬ c → OkDAt σ P (g ())) :
    OkDAt σ P (NonDetE.whenE c (NonDetE.throwError e) >>= g) := by
  refine okdAt_bind fun a s h => ?_
  unfold NonDetE.whenE at h
  split at h
  · have e := Set.mem_singleton_iff.1 h; simp at e
  · rename_i hc
    have e := Set.mem_singleton_iff.1 h
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    exact hg hc

theorem okdAt_returnOk_bind {P : State Unit → β → Prop} {v : α} {g : α → NonDetE (State Unit) ε β}
    (hg : OkDAt σ P (g v)) : OkDAt σ P (NonDetE.returnOk v >>= g) := by
  refine okdAt_bind fun a s h => ?_
  have e := Set.mem_singleton_iff.1 h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact hg

theorem okdAt_gets_bind {P : State Unit → β → Prop} {f : State Unit → α} {g : α → NonDetE (State Unit) ε β}
    (hg : OkDAt σ P (g (f σ))) : OkDAt σ P (NonDetE.liftE (NonDet.gets f) >>= g) := by
  refine okdAt_bind fun a s h => ?_
  obtain ⟨x, hx, e⟩ := mem_liftE_inv' h
  obtain rfl := Set.mem_singleton_iff.1 hx
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact hg

theorem okdAt_liftME {P : State Unit → β → Prop} {g : α → β} {m : NonDetE (State Unit) ε α}
    (h : OkDAt σ (fun s a => P s (g a)) m) : OkDAt σ P (NonDetE.liftME g m) := by
  unfold NonDetE.liftME
  refine okdAt_bind fun a s ha => ?_
  exact okdAt_returnOk (h a s ha)

theorem okdAt_ite {P : State Unit → α → Prop} (c : Prop) [Decidable c] {m1 m2 : NonDetE (State Unit) ε α}
    (h1 : OkDAt σ P m1) (h2 : OkDAt σ P m2) : OkDAt σ P (if c then m1 else m2) := by
  split <;> assumption

end OkD

theorem okd_setStart (args : List Data) (σ : State Unit) :
    OkDAt σ (fun s d => DomInvOK s (.invokeDomain d)) (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart
  refine okdAt_whenE_bind _ _ fun _ => okdAt_returnOk_bind (okdAt_gets_bind
    (okdAt_whenE_bind _ _ fun h2 => okdAt_whenE_bind _ _ fun h3 => okdAt_returnOk ?_))
  refine ⟨by omega, fun e => h3 ?_⟩
  rw [e]; rfl

theorem maxDomainDuration_toNat : (maxDomainDuration : BitVec 64).toNat = 2 ^ domainDurationLen - 1 := by
  decide

theorem okd_configure (hnd : numDomains = 1) (args : List Data) (σ : State Unit) :
    OkDAt σ (fun s d => DomInvOK s (.invokeDomain d)) (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure
  refine okdAt_whenE_bind _ _ fun _ => okdAt_returnOk_bind (okdAt_returnOk_bind (okdAt_returnOk_bind
    (okdAt_gets_bind (okdAt_whenE_bind _ _ fun h2 => okdAt_whenE_bind _ _ fun h3 =>
      okdAt_whenE_bind _ _ fun h4 => okdAt_whenE_bind _ _ fun _ => okdAt_gets_bind
        (okdAt_whenE_bind _ _ fun h6 => okdAt_returnOk ?_)))))
  refine ⟨by omega, ?_, fun e hz => h6 ⟨e, ?_⟩⟩
  · rw [hnd] at h3
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth]
    have : (the args[1]? : Data).toNat = 0 := by simp only [unat] at h3; omega
    rw [this]; rfl
  · have h4' : (parseTimeArg 2 args).toNat ≤ (maxDomainDuration : BitVec 64).toNat := by
      rw [gt_iff_lt, BitVec.not_lt, BitVec.le_def] at h4; exact h4
    rw [maxDomainDuration_toNat] at h4'
    have hz' := congrArg BitVec.toNat hz
    rw [BitVec.toNat_setWidth] at hz'
    apply BitVec.eq_of_toNat_eq
    have hp : 0 < 2 ^ domainDurationLen := Nat.two_pow_pos _
    rw [Nat.mod_eq_of_lt (by omega)] at hz'
    exact hz'

theorem okd_decodeDomain (hnd : numDomains = 1) (label : Data) (args : List Data) (ex : List (Cap × CslotPtr))
    (σ : State Unit) :
    OkDAt σ (fun s d => DomInvOK s (.invokeDomain d)) (decodeDomainInvocation (Z := Unit) label args ex) := by
  unfold decodeDomainInvocation
  split
  · unfold decodeDomainSet
    refine okdAt_bind fun _ _ _ => okdAt_whenE_bind _ _ fun _ => ?_
    split
    · exact okdAt_returnOk trivial
    · exact okdAt_throw _
  · exact okd_configure hnd args σ
  · exact okd_setStart args σ
  · exact okdAt_throw _

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `DomInvOK`** at the decode's end
state. -/
theorem okd_fl4Decode (hnd : numDomains = 1) (fp : Bool) (label : Data) (args : List Data) (ci : CapRef)
    (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ DomInvOK (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk trivial
    | exact okdAt_liftME (fun _ _ _ => trivial)
    | exact okdAt_liftME (okd_decodeDomain hnd _ _ _ σ)
    | (apply okdAt_ite)
    | split)

/-! ## The perform and the invocation shell -/

/-- **Every perform keeps `DomListOK`**, from `DomInvOK` at its start. -/
theorem dpe_perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit) (x : Except Unit (List Data) × State Unit)
    (hs : DomListOK σ) (hi : DomInvOK σ inv) (hx : x ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1) :
    DomListOK x.2 := by
  by_cases hd : ∃ d, inv = .invokeDomain d
  · obtain ⟨d, rfl⟩ := hd
    simp only [fl4PerformInvocation] at hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    obtain ⟨z, hz, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact dp_invokeDomain d σ z hs hi hz
  · exact dpe_of_dle (dle_fl4Perform blk call don inv fun d e => hd ⟨d, e⟩) σ x hs hx

/-- The `syscall` shell, pointwise (sch12's `syscall_post`, XTopJointMidRunS). -/
theorem syscall_post' {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ : State Unit} {I Q : State Unit → Prop}
    (h1 : ∀ w ∈ ((ExceptT.run mF) σ).1, I w.2)
    (h2 : ∀ f s, I s → ∀ v ∈ (hF f s).1, Q v.2)
    (h3 : ∀ a s, (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → ∀ w ∈ ((ExceptT.run (mE a)) s).1, I w.2)
    (h4 : ∀ e s, I s → ∀ v ∈ (hE e s).1, Q v.2)
    (h5 : ∀ a s b s', (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → (.ok b, s') ∈ ((ExceptT.run (mE a)) s).1 →
      I s' → ∀ y ∈ ((mFin b).run s').1, Q y.2) :
    ∀ y ∈ ((syscall mF hF mE hE mFin).run σ).1, Q y.2 := by
  intro y hy
  unfold syscall withoutPreemption at hy
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
  · obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
    simp only [Except.ok.injEq] at hr
    subst hr
    obtain ⟨r, s⟩ := w
    cases r with
    | error f =>
      obtain ⟨v, hv, rfl⟩ := mem_liftE_inv' hy
      exact h2 f s (h1 _ hw) v hv
    | ok a =>
      obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨w, hw', rfl⟩ := mem_liftE_inv' hz
        simp only [Except.ok.injEq] at hr
        subst hr
        obtain ⟨r, s'⟩ := w
        cases r with
        | error e =>
          obtain ⟨v, hv, rfl⟩ := mem_liftE_inv' hy
          exact h4 e s' (h3 a s hw _ hw') v hv
        | ok b => exact h5 a s b s' hw hw' (h3 a s hw _ hw') y hy
      · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz
        cases he
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz
    cases he

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `DomListOK`.** -/
theorem dpe_handleInvocationR (hnd : numDomains = 1) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    DPE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine dpe_bind (dpe_of_dle (by dl_auto)) fun thread => dpe_bind (dpe_of_dle (by dl_auto)) fun info => ?_
  intro σ y hs hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, DomListOK w.2 :=
    fun w hw => dpe_of_dle (by dl_auto) σ w hs hw
  refine syscall_post' (I := DomListOK) (Q := DomListOK) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact dp_of_dl (by dl_auto) s v hs hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact dpe_of_dle (by dl_auto) s w (h1 _ has) hw
  · intro e s hs v hv; exact dp_of_dl (by dl_auto) s v hs hv
  · intro a s b s' _ hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hd : DomInvOK s' b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode hnd _ _ _ _ _ _ _ _ s1) b s' hbs
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz' : dlV z.2 = dlV s' := (by dl_auto : DLE (withoutPreemption (Z := Unit)
        (setThreadState thread .restart))) s' z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hs1 : DomListOK s1 := domListOK_of_dlV hz' hI
      have hd1 : DomInvOK s1 b := domInvOK_of_dlV hz' hd
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := dpe_perform blocking calling don b s1 _ hs1 hd1 hz2
        exact dpe_of_dle (by dl_auto) s2 y hs2 hy
      · exact dpe_perform blocking calling don b s1 _ hs1 hd1 hz2
    · exact domListOK_of_dlV ((by dl_auto : DLE (withoutPreemption (Z := Unit)
        (setThreadState thread .restart))) s' z hz) hI

/-! ## The kernel entry -/

macro_rules | `(tactic| dp_leaf) => `(tactic| (refine dpe_handleInvocationR ?_ _ _ _ _ _ _; assumption))

set_option maxHeartbeats 8000000 in
theorem dpe_fl4HandleSyscall (hnd : numDomains = 1) (rep : Bool) (c : Syscall) :
    DPE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> dp_auto

set_option maxHeartbeats 4000000 in
theorem dpe_fl4HandleEvent (hnd : numDomains = 1) (rep : Bool) (ev : Event) :
    DPE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine dpe_bind (dpe_of_dle (by dl_auto)) fun _ => dpe_bind (dpe_of_dle (by dl_auto)) fun _ =>
      dpe_whenE _ (dpe_fl4HandleSyscall hnd rep c)
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact dpe_of_dle (dle_handleEvent_other ev fun c e => h ⟨c, e⟩)

set_option maxHeartbeats 4000000 in
/-- **`fl4CallKernel` keeps `DomListOK`, for every event** (the syscall,
interrupt, fault and unknown-syscall entries). -/
theorem dp_fl4CallKernel (hnd : numDomains = 1) (rep : Bool) (ev : Event) :
    DP (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine dp_bind (dpe_handleE (dpe_fl4HandleEvent hnd rep ev) fun _ => dpe_of_dle (by dl_auto)) fun _ => ?_
  refine dp_bind (dp_of_dl dl_fl4Awaken) fun _ => dp_bind dp_schedule fun _ => dp_of_dl dl_activateThread

theorem dp_fl4KernelEntrySyscall (hnd : numDomains = 1) (rep : Bool) (c : Syscall) :
    DP (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact dp_bind (dp_of_dl (dk_gets _)) fun ct => dp_bind (dp_of_dl (dl_fl4SyscallFaultIP ct)) fun _ =>
    dp_fl4CallKernel hnd rep _

/-! ## Tops -/

/-- **(b) `DomListOK` across a whole syscall entry.** `hnd : numDomains = 1`
[P] (FL4's configuration; the decode of DomainScheduleConfigure checks
`domain < numDomains`, and `DomListOK.dom` asks every entry's domain to be 0). -/
theorem kentry_domListOK (hnd : numDomains = 1) {c : Syscall} {σ : State Unit} (h : DomListOK σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c σ).1), DomListOK y.2 :=
  fun y hy => dp_fl4KernelEntrySyscall hnd true c σ y h hy

/-- **(c) `DomListOK` across the interrupt / timer entry** (`fl4CallKernel`
with `.interrupt`; Fl4Spec's Ext/Entry has no separate interrupt entry, so this
is `dp_fl4CallKernel` at that event; the same holds for every event). -/
theorem kirq_domListOK (hnd : numDomains = 1) {σ : State Unit} (h : DomListOK σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) true .interrupt σ).1), DomListOK y.2 :=
  fun y hy => dp_fl4CallKernel hnd true .interrupt σ y h hy

/-- **(d) `DomListOK` at Fl4Spec's initial state** (`initASt`: the list
`[(0, -1), (0, 0)]`, start and index 0). -/
theorem domListOK_init : DomListOK (initASt (Z := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initASt]
  · intro e he _; simp only [initASt, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  · simp [initASt]
  · simp only [initASt, domainEndMarker]; decide
  · simp only [initASt, domainEndMarker]; decide
  · simp [initASt]
  · intro e he; simp only [initASt, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl

end

end Fl4Proofs.P3.SInvDom
