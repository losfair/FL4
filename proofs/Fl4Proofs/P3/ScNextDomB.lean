/-
P3 (DESIGN.md §9), scheduler: **the domain switch's pieces at
`SchedRel`** (KENTRY-PLAN.md sch3 (b)), for the `domainTime = 0` case of
`schedule_choose_new_thread`.

* `DI`: a spec computation keeps `domain_index` (`di_awaken`: the spec's
  `awaken`); the scheduler-step framework's `SchStep`/`SOK` keep the domain
  list and start, not the index (which `next_domain` writes).
* `NdW`: the kernel-global words `next_domain` writes besides the node's
  `REPROGRAM` (`DOMAIN_TIME`, `DOM_SCHED_IDX`, `WORK_UNITS`; `CUR_DOMAIN` is
  written with its value 0); `SFootN`: `SFoot` with them.
* `TK0`: `TK` without the domain time.
* `NdOK`: what `next_domain_eq`/`nextDomain_eq` need at a state: `DomRel`,
  `DomListOK` [J] and `DOM_SCHED_IDX = domain_index` [J] (ScNextDom).
* `ArchNd` [P]: the spec's `arch_prepare_next_domain` (l4v
  `Arch_A.X64_A.arch_prepare_next_domain = switch_local_fpu_owner None`;
  FL4 does nothing there) at every related state, in `ArchSw`'s form (one
  outcome, `SchedRel`/`NtfnStateRel` kept with FL4's store unchanged,
  `ArchKeeps`). NOT TRUE in every reachable state: when the spec has an FPU
  owner `t` (`x64_current_fpu_owner = some t`, set by `lazy_fpu_restore` in
  every `arch_switch_to_thread` to a thread without `fpuDisabled`), the
  outcome saves the machine FPU image into `t`'s `tcbArch` and clears its
  `tcbCurFpu`, so `kheap` changes (only inside `t`'s `tcbArch`, which no
  relation reads). The same holds for `ArchSw`'s `arch_switch_to_thread`
  (KENTRY-PLAN.md sch2/sch3 (d)); both are to be replaced together by a
  `kheap`-up-to-`tcbArch` frame.
* `schedRel_ndS` / `ntfnRel_ndS`: `SchedRel` / `NtfnStateRel` from `s, σ` to
  FL4's `ndS s t` and the spec's `ndSt σ t.bv`; `ndS_writes`: its footprint.
* `scnt_refines0`: `schedule_choose_new_thread` for either domain time
  (the 0 case from `NdOK` and `ArchNd`).
-/
import Fl4Proofs.P3.ScNextDom
import Fl4Proofs.P3.ScPresOps
import Fl4Proofs.P3.XTopStep
import Fl4Proofs.P3.DomSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-! ## `domain_index` kept -/

/-- Every outcome keeps `domain_index`. -/
def DI {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → x.2.domainIndex = σ.domainIndex

theorem DI.of_eq {α : Type} {m : NonDet (State Unit) α} (h : DI m) {σ σ' : State Unit} {a : α} {X : Prop}
    (he : m σ = ({(a, σ')}, X)) : σ'.domainIndex = σ.domainIndex :=
  h σ (a, σ') (by rw [he]; exact Set.mem_singleton _)

theorem di_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : DI m)
    (hg : ∀ a, DI (g a)) : DI (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hg y.1 y.2 x hx).trans (hm σ y hy)

theorem di_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : DI m)
    (hg : ∀ a, DI (g a)) : DI (NonDet.bind m g) := di_bind hm hg

theorem di_pure {α : Type} (a : α) : DI (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem di_pure' {α : Type} (a : α) : DI (NonDet.pure a : NonDet (State Unit) α) := di_pure a

theorem di_gets {α : Type} (g : State Unit → α) : DI (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem di_get : DI (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem di_assert (P : Prop) : DI (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem di_fail {α : Type} : DI (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem di_assertOpt {α : Type} (o : Option α) : DI (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact di_fail
  · exact di_pure' _

theorem di_getsThe {α : Type} (g : State Unit → Option α) : DI (NonDet.getsThe g) := by
  intro σ x hx; exact di_assertOpt (g σ) σ x hx

theorem di_selectF {α : Type} (S : Set α × Prop) : DI (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]

theorem di_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : DI m1)
    (h2 : DI m2) : DI (if P then m1 else m2) := by
  split <;> assumption

theorem di_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : DI m) :
    DI (NonDet.when P m) := by
  unfold NonDet.when; exact di_ite P h (di_pure' _)

theorem di_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, DI (g a)) (o : Option α) :
    DI (NonDet.maybeM g o) := by
  cases o
  · exact di_pure' _
  · exact h _

theorem di_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).domainIndex = σ.domainIndex) :
    DI (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem di_setObject (p : ObjRef) (o : KernelObject) : DI (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := Sched.setObject_mem hx
  rw [e]

theorem di_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, DI (B r)) (r : α) : DI (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => rfl
  | step _ hm _ ih => exact ih.trans (hB _ _ _ hm)

theorem di_doExtendedOp (eop : DetExtMonad Unit) : DI (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine di_bind di_get (fun _ => di_bind (di_selectF _) (fun _ => ?_))
  split
  exact di_modify (fun σ => rfl)

/-- One step of a `DI` proof. -/
macro "di_step" : tactic => `(tactic| first
  | with_reducible exact di_pure _ | with_reducible exact di_pure' _ | with_reducible exact di_fail
  | with_reducible exact di_gets _ | with_reducible exact di_get
  | with_reducible exact di_assert _ | with_reducible exact di_assertOpt _
  | with_reducible exact di_getsThe _ | with_reducible exact di_selectF _
  | with_reducible exact di_setObject _ _ | with_reducible exact di_getObject _ | with_reducible exact di_doExtendedOp _
  | ((with_reducible apply di_modify); intro _; rfl)
  | (with_reducible refine di_bind ?_ (fun _ => ?_))
  | (with_reducible refine di_bind' ?_ (fun _ => ?_))
  | (with_reducible apply di_ite) | (with_reducible apply di_when)
  | (with_reducible refine di_maybeM (fun _ => ?_) _)
  | (with_reducible refine di_whileLoop (fun _ => ?_) _)
  | split
  | (dsimp only))

theorem di_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : DI (threadGet (Z := Unit) g p) := by
  unfold threadGet; repeat di_step

theorem di_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    DI (tcbSchedAction (Z := Unit) a t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  refine di_bind (di_threadGet _ _) fun _ => di_bind (di_threadGet _ _) fun _ => ?_
  repeat di_step

theorem di_getObject (p : ObjRef) : DI (getObject (Z := Unit) p) := di_getsThe _

theorem di_getSchedContext (p : ObjRef) : DI (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext
  refine di_bind (di_getObject p) fun k => ?_
  split
  · exact di_pure _
  · exact di_fail

theorem di_rescheduleRequired : DI (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction getScRefillSufficient getScRefillReady
  repeat (first | with_reducible exact di_threadGet _ _ | with_reducible exact di_getSchedContext _ | with_reducible exact di_tcbSchedAction _ _ | di_step)

theorem di_tcbReleaseRemove (t : ObjRef) : DI (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue
  repeat (first | with_reducible exact di_threadGet _ _ | with_reducible exact di_getSchedContext _ | with_reducible exact di_tcbSchedAction _ _ | di_step)

theorem di_possibleSwitchTo (t : ObjRef) : DI (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef setSchedulerAction
  repeat (first | with_reducible exact di_threadGet _ _ | with_reducible exact di_rescheduleRequired | with_reducible exact di_tcbSchedAction _ _ | di_step)

/-- **The spec's `awaken` keeps `domain_index`.** -/
theorem di_awaken : DI (awaken (Z := Unit)) := by
  unfold awaken tcbReleaseDequeue
  repeat (first | with_reducible exact di_tcbReleaseRemove _ | with_reducible exact di_possibleSwitchTo _ | di_step)

/-- `TK` without the domain time (`next_domain` installs a new one). -/
def TK0 (σ σ' : State Unit) : Prop :=
  σ'.curTime = σ.curTime ∧ σ'.consumedTime = σ.consumedTime ∧ σ'.idleThread = σ.idleThread ∧
    σ'.curDomain = σ.curDomain ∧ σ'.idleSc = σ.idleSc

theorem TK.tk0 {σ σ' : State Unit} (h : Sched.TK σ σ') : TK0 σ σ' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem TK0.trans {σ1 σ2 σ3 : State Unit} (h1 : TK0 σ1 σ2) (h2 : TK0 σ2 σ3) : TK0 σ1 σ3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- The kernel-global words `next_domain` writes besides `REPROGRAM` and
`CUR_DOMAIN` (written with its value 0): `DOMAIN_TIME`, `DOM_SCHED_IDX`,
`WORK_UNITS`. -/
def NdW (kb b : U64) : Prop := b = ksW kb 16#u64 ∨ b = ksW kb 24#u64 ∨ b = ksW kb 40#u64

/-- The scheduler footprint with `next_domain`'s kernel-global words. -/
def SFootN (st : machine.Store S) [L : P1.LawfulStore st] (T : Set U64) (c : U64) (s : S) (b : U64) : Prop :=
  SFoot st T c s b ∨ NdW (L.ksb s) b

theorem WritesIn.sfootN_of {T : Set U64} {c : U64} {s s' : S} (h : P1.WritesIn st s s' (SFoot st T c s)) :
    P1.WritesIn st s s' (SFootN st T c s) := h.mono fun _ hb => Or.inl hb

theorem WritesIn.sfootN_trans {T : Set U64} {c : U64} {s s1 s2 : S} (h1 : P1.WritesIn st s s1 (SFootN st T c s))
    (h2 : P1.WritesIn st s1 s2 (SFootN st T c s1)) : P1.WritesIn st s s2 (SFootN st T c s) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb | hb
    · exact hb
    · exact Or.inl ((SFoot.ksb h1.1).1 hb)
    · rw [h1.1] at hb; exact Or.inr hb

/-- What `next_domain` reads at a state (ScNextDom): the domain relation,
`DomListOK` [J] and `DOM_SCHED_IDX = domain_index` [J] (l4v has no
counterpart of FL4's index word; true at every reachable state with the
two-entry table: boot 0/0, ScheduleSetStart 0 / `length - 2`, `next_domain`
the start index on both sides). -/
def NdOK (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  DomRel (L.mem s) (L.ksb s) σ ∧ DomListOK σ ∧ (L.mem s (ksW (L.ksb s) 24#u64)).val = σ.domainIndex

/-- **`arch_prepare_next_domain`** [P] (module docstring: NOT TRUE when the
spec has an FPU owner). -/
def ArchNd (st : machine.Store S) [L : P1.LawfulStore st] (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    ∃ σ1, Fl4Spec.archPrepareNextDomain (Z := Unit) σ = ({((), σ1)}, False) ∧ SchedRel st N T C c s σ1 ∧
      NtfnStateRel N T (L.mem s) σ1 ∧ ArchKeeps σ σ1 ∧ σ1.domainList = σ.domainList ∧
      σ1.domainIndex = σ.domainIndex ∧ σ1.domainStartIndex = σ.domainStartIndex

theorem ks_fit {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) :
    (L.ksb s).val + 13568 ≤ 2 ^ 64 ∧ (L.ksb s).val % 8 = 0 := by
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hf := hc.node.fits
  have hal := hc.node.align
  simp only [P1.LawfulStore.nodeBase] at hf hal
  omega

theorem dtA_ks (s : S) : dtA st s = ksW (L.ksb s) 16#u64 := rfl
theorem curDomA_ks (s : S) : curDomA st s = ksW (L.ksb s) 8#u64 := rfl

/-- **`next_domain`'s footprint**: `NdW` and the node's `REPROGRAM`, the
`CUR_DOMAIN` word being 0. -/
theorem ndS_writes {s : S} (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hR : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.REPROGRAM))
    (hRk : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.REPROGRAM).val ≠ (ksW (L.ksb s) o).val)
    (h8 : L.mem s (ksW (L.ksb s) 8#u64) = 0#u64) (t : U64) :
    P1.WritesIn st s (ndS (L := L) s t)
      (fun b => NdW (L.ksb s) b ∨ b = L.nodeAt s (L.cpu s) layout.node.REPROGRAM) := by
  set kb := L.ksb s
  set R := L.nodeAt s (L.cpu s) layout.node.REPROGRAM
  have a24 := ksW_al (o := 24#u64) hkf hka (by decide) (by decide)
  have a40 := ksW_al (o := 40#u64) hkf hka (by decide) (by decide)
  have a8 := ksW_al (o := 8#u64) hkf hka (by decide) (by decide)
  have a16 := ksW_al (o := 16#u64) hkf hka (by decide) (by decide)
  have w1 : P1.WritesIn st s (L.wr s (ksW kb 24#u64) 0#u64) (fun b => NdW kb b ∨ b = R) :=
    (P1.writesIn_wr a24).mono fun b e => Or.inl (Or.inr (Or.inl e))
  set s1 := L.wr s (ksW kb 24#u64) 0#u64
  have w2 : P1.WritesIn st s1 (L.wr s1 R 1#u64) (fun b => NdW kb b ∨ b = R) :=
    (P1.writesIn_wr hR).mono fun b e => Or.inr e
  set s2 := L.wr s1 R 1#u64
  have w3 : P1.WritesIn st s2 (L.wr s2 (ksW kb 40#u64) 0#u64) (fun b => NdW kb b ∨ b = R) :=
    (P1.writesIn_wr a40).mono fun b e => Or.inl (Or.inr (Or.inr e))
  set s3 := L.wr s2 (ksW kb 40#u64) 0#u64
  have e8 : L.mem s3 (ksW kb 8#u64) = 0#u64 := by
    rw [mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [L.mem_wr_ne hR a8 (hRk 8#u64 (by decide))]
    rw [mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h8
  have w4 : P1.WritesIn st s3 (L.wr s3 (ksW kb 8#u64) 0#u64) (fun b => NdW kb b ∨ b = R) := by
    have := writesIn_same (st := st) (s := s3) a8
    rw [e8] at this
    exact this.mono fun _ h => h.elim
  set s4 := L.wr s3 (ksW kb 8#u64) 0#u64
  have w5 : P1.WritesIn st s4 (L.wr s4 (ksW kb 16#u64) t) (fun b => NdW kb b ∨ b = R) :=
    (P1.writesIn_wr a16).mono fun b e => Or.inl (Or.inl e)
  exact wtrans (wtrans (wtrans (wtrans w1 w2) w3) w4) w5

/-- A kernel-global word below 256 is outside the notification relation's
footprint (the notifications and TCBs off the block, `hNk`, `ksOut`). -/
theorem footEq_ks {N T : Set U64} (hP : NPlaced T N) {kb : U64}
    (hT : ∀ t ∈ T, t.val + 2 ^ 12 ≤ kb.val ∨ kb.val + 13568 ≤ t.val)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ kb.val ∨ kb.val + 13568 ≤ n.val) {s : S} {a : U64} (ha : P1.Aligned a)
    (hav : kb.val ≤ a.val ∧ a.val < kb.val + 256) (v : U64) :
    FootEq N T (L.mem s) (L.mem (L.wr s a v)) := by
  intro b hb hf
  refine L.mem_wr_ne ha hb ?_
  rcases hf with ⟨n, hn', h1, h2⟩ | ⟨t, ht', e⟩
  · have := hNk n hn'; omega
  · have hta := hP.tcb t ht'
    have := hT t ht'
    rcases e with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tStA_eq, tfield_val hta (by simp)]; simp; omega
    · rw [tBlockA_eq, tfield_val hta (by simp)]; simp; omega
    · rw [badgeRegA_eq, tfield_val hta (by simp)]; simp; omega
    · rw [prioA_eq', tfield_val hta (by simp)]; simp; omega
    · rw [nextEp_eq, tfield_val hta (by simp)]; simp; omega
    · rw [prevEp_eq, tfield_val hta (by simp)]; simp; omega

theorem dt_of {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit} {F : U64 → Prop}
    (hS : SchedRel st N T C c s σ) (hw : P1.WritesIn st s s' F) (ha : P1.Aligned (dtA st s))
    (hn : ¬ F (dtA st s)) : σ.domainTime = (L.mem s' (dtA st s)).bv := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  rw [hw.mem_eq ha hn]; exact hs.domTime

theorem ksW_ne {kb : U64} (hkf : kb.val + 13568 ≤ 2 ^ 64) {o o' : U64} (ho : o.val < 256) (ho' : o'.val < 256)
    (h : o.val ≠ o'.val) : ksW kb o ≠ ksW kb o' := fun e => by
  have := congrArg UScalar.val e
  rw [ksW_val (by omega), ksW_val (by omega)] at this; omega

set_option maxHeartbeats 1000000 in
/-- **`SchedRel` across `next_domain`**: FL4's `ndS s t` and the spec's
`ndSt σ t.bv` (the reprogram flag set, the domain 0 kept, the domain time
`t`; the index and work units are read by no scheduler relation). -/
theorem schedRel_ndS {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (t : U64) :
    SchedRel st N T C c (ndS (L := L) s t) (ndSt σ t.bv) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hkf, hka⟩ := ks_fit hS
  set kb := L.ksb s with hkb
  have a24 := ksW_al (o := 24#u64) hkf hka (by decide) (by decide)
  have a40 := ksW_al (o := 40#u64) hkf hka (by decide) (by decide)
  have a8 := ksW_al (o := 8#u64) hkf hka (by decide) (by decide)
  have a16 := ksW_al (o := 16#u64) hkf hka (by decide) (by decide)
  -- DOM_SCHED_IDX
  have h1 : SchedRel st N T C c (L.wr s (ksW kb 24#u64) 0#u64) σ :=
    hS.domW (writesIn_ksW s 0#u64 hkf hka (o := 24#u64) (by simp)) (SchedK.refl σ) rfl rfl
      (dt_of hS (P1.writesIn_wr a24) a16 (ksW_ne hkf (by decide) (by decide) (by decide)))
  set s1 := L.wr s (ksW kb 24#u64) 0#u64
  have hk1 : L.ksb s1 = kb := L.ksb_wr _ _ _
  -- REPROGRAM
  have e1 : L.nodeAt s1 c layout.node.REPROGRAM = L.nodeAt s (L.cpu s) layout.node.REPROGRAM := by
    rw [Sched.nodeAt_ksb hk1, hc.cur]
  have h2 := h1.set_reprogram.1
  rw [e1] at h2
  set s2 := L.wr s1 (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64
  have hk2 : L.ksb s2 = kb := (L.ksb_wr _ _ _).trans hk1
  -- WORK_UNITS
  have v40 : (40#u64 : U64).val = 40 := rfl
  have hw3 : P1.WritesIn st s2 (L.wr s2 (ksW kb 40#u64) 0#u64) (KsW (L.ksb s2)) :=
    (P1.writesIn_wr a40).mono fun b e => ⟨40#u64, by decide, by decide, by decide,
      by rw [e, ksW_val (by rw [v40]; omega), hk2], Or.inl (by decide)⟩
  have h3 := Sched.SchedRel.ksW h2 hw3
  set s3 := L.wr s2 (ksW kb 40#u64) 0#u64
  have hk3 : L.ksb s3 = kb := (L.ksb_wr _ _ _).trans hk2
  -- CUR_DOMAIN, written with its value 0
  have e8 : L.mem s3 (ksW kb 8#u64) = 0#u64 := by
    obtain ⟨Q3, R3, hc3, hs3⟩ := h3.lists
    have := hs3.curDom.2
    rw [curDomA_ks, hk3] at this; exact this
  have hw4 : P1.WritesIn st s3 (L.wr s3 (ksW kb 8#u64) 0#u64) (fun _ => False) := by
    have := writesIn_same (st := st) (s := s3) a8
    rw [e8] at this; exact this
  have h4 : SchedRel st N T C c (L.wr s3 (ksW kb 8#u64) 0#u64) { σ with reprogramTimer := true } :=
    h3.domW (hw4.mono fun _ h => h.elim) (SchedK.refl _) rfl rfl
      (dt_of h3 hw4 (by rw [dtA_ks, hk3]; exact a16) id)
  set s4 := L.wr s3 (ksW kb 8#u64) 0#u64
  have hk4 : L.ksb s4 = kb := (L.ksb_wr _ _ _).trans hk3
  -- DOMAIN_TIME
  have hK : SchedK { σ with reprogramTimer := true } (ndSt σ t.bv) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs.curDom.1.symm, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine h4.domW ((writesIn_ksW s4 t hkf hka (o := 16#u64) (by simp)).mono fun b hb => by rw [hk4]; exact hb)
    hK rfl rfl ?_
  show t.bv = (L.mem (L.wr s4 (ksW kb 16#u64) t) (ksW (L.ksb s4) 16#u64)).bv
  rw [hk4, mem_ks_same _ _ hkf hka (by decide) (by decide)]

/-- **`NtfnStateRel` across `next_domain`** (kernel-global words and the
node's `REPROGRAM`, none in the notification footprint). -/
theorem ntfnRel_ndS {N T C : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val) (hk : σ'.kheap = σ.kheap)
    (t : U64) : NtfnStateRel N T (L.mem (ndS (L := L) s t)) σ' := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hkf, hka⟩ := ks_fit hS
  have hP := hS.placed
  have hT : ∀ t ∈ T, t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := hc.ksOut
  have kv : ∀ o : U64, o.val < 256 → (L.ksb s).val ≤ (ksW (L.ksb s) o).val ∧
      (ksW (L.ksb s) o).val < (L.ksb s).val + 256 := fun o ho => by rw [ksW_val (by omega)]; omega
  have hRw : FootEq N T (L.mem (L.wr s (ksW (L.ksb s) 24#u64) 0#u64))
      (L.mem (L.wr (L.wr s (ksW (L.ksb s) 24#u64) 0#u64) (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)) := by
    have h1 : SchedRel st N T C c (L.wr s (ksW (L.ksb s) 24#u64) 0#u64) σ :=
      hS.domW (writesIn_ksW s 0#u64 hkf hka (o := 24#u64) (by simp)) (SchedK.refl σ) rfl rfl
        (dt_of hS (P1.writesIn_wr (ksW_al hkf hka (by decide) (by decide))) (ksW_al hkf hka (by decide) (by decide))
          (ksW_ne hkf (by decide) (by decide) (by decide)))
    have := node_wr_foot h1 (o := layout.node.REPROGRAM) (v := 1#u64) (by simp [layout.node.REPROGRAM])
      (by simp [layout.node.REPROGRAM])
    rwa [Sched.nodeAt_ksb (L.ksb_wr _ _ _), ← hc.cur] at this
  have f := fun (s0 : S) (o : U64) (ho : o.val < 256) (h8 : o.val % 8 = 0) (v : U64) =>
    footEq_ks (st := st) hP hT hNk (s := s0) (ksW_al hkf hka ho h8) (kv o ho) v
  have hm : FootEq N T (L.mem s) (L.mem (ndS (L := L) s t)) := by
    intro a ha hfa
    unfold ndS
    rw [f _ 16#u64 (by decide) (by decide) t a ha hfa, f _ 8#u64 (by decide) (by decide) _ a ha hfa,
      f _ 40#u64 (by decide) (by decide) _ a ha hfa, hRw a ha hfa, f _ 24#u64 (by decide) (by decide) _ a ha hfa]
  exact hR.frame hP hm (KView.of_kheap hk)

theorem DomListOK.congr {σ σ' : Fl4Spec.State Unit} (h : DomListOK σ) (hdl : σ'.domainList = σ.domainList)
    (hdi : σ'.domainIndex = σ.domainIndex) (hds : σ'.domainStartIndex = σ.domainStartIndex) : DomListOK σ' :=
  ⟨by rw [hdl]; exact h.len, by rw [hdl]; exact h.zero, by rw [hdl, hds]; exact h.start,
    by rw [hdl, hds]; exact h.startNE, by rw [hdl]; exact h.last, by rw [hdl, hdi]; exact h.idx,
    by rw [hdl]; exact h.dom⟩

/-- A kernel-global word below 256 is no scheduler-footprint word. -/
theorem ks_not_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {o : U64} (ho : o.val < 256) : ¬ SFoot st T c s (ksW (L.ksb s) o) := by
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  obtain ⟨hkf, -⟩ := ks_fit hS
  intro h
  rcases SFoot.range hc.tcbs h with ⟨y, hy, h1, h2⟩ | ⟨g1, g2⟩
  · rw [ksW_val (by omega)] at h1 h2; rcases hc.ksOut y hy with e | e <;> omega
  · rw [ksW_val (by omega)] at g1 g2; simp only [P1.LawfulStore.nodeBase] at g1; omega

theorem NdOK.keep {s s' : S} {σ σ' : Fl4Spec.State Unit} (h : NdOK (L := L) s σ) (hk : L.ksb s' = L.ksb s)
    (hm : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → L.mem s' (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o))
    (hdl : σ'.domainList = σ.domainList) (hdi : σ'.domainIndex = σ.domainIndex)
    (hds : σ'.domainStartIndex = σ.domainStartIndex) : NdOK (L := L) s' σ' := by
  obtain ⟨hD, hV, hi⟩ := h
  refine ⟨?_, hV.congr hdl hdi hds, ?_⟩
  · rw [hk]
    refine hD.of_same (domSame_iff fun o ho => hm o ?_ ?_) hdl hds <;>
      (simp only [domOffs, List.mem_cons, List.mem_nil_iff, or_false] at ho
       rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [hk, hm 24#u64 (by decide) (by decide), hdi]; exact hi

theorem NdOK.sfoot {N T C : Set U64} {c : U64} {s s' : S} {σ σ0 σ' : Fl4Spec.State Unit} (h : NdOK (L := L) s σ)
    (hS : SchedRel st N T C c s σ0) (hw : P1.WritesIn st s s' (SFoot st T c s))
    (hdl : σ'.domainList = σ.domainList) (hdi : σ'.domainIndex = σ.domainIndex)
    (hds : σ'.domainStartIndex = σ.domainStartIndex) : NdOK (L := L) s' σ' := by
  obtain ⟨hkf, hka⟩ := ks_fit hS
  exact h.keep hw.1 (fun o ho h8 => hw.mem_eq (ksW_al hkf hka ho h8) (ks_not_sfoot hS ho)) hdl hdi hds

/-- `NdOK.sfoot` with the scheduler relation at the later state. -/
theorem NdOK.sfoot' {N T C : Set U64} {c : U64} {s s' : S} {σ σ0 σ' : Fl4Spec.State Unit} (h : NdOK (L := L) s σ)
    (hS' : SchedRel st N T C c s' σ0) (hw : P1.WritesIn st s s' (SFoot st T c s))
    (hdl : σ'.domainList = σ.domainList) (hdi : σ'.domainIndex = σ.domainIndex)
    (hds : σ'.domainStartIndex = σ.domainStartIndex) : NdOK (L := L) s' σ' := by
  obtain ⟨hkf, hka⟩ := ks_fit hS'
  rw [hw.1] at hkf hka
  refine h.keep hw.1 (fun o ho h8 => hw.mem_eq (ksW_al hkf hka ho h8) fun hb => ks_not_sfoot hS' ho ?_) hdl hdi hds
  rw [hw.1]; exact (SFoot.ksb hw.1).2 hb

/-- `KFoot` with `next_domain`'s kernel-global words. -/
def KFootN (st : machine.Store S) [L : P1.LawfulStore st] (T N C : Set U64) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  KFoot st T N C c s σ b ∨ NdW (L.ksb s) b

theorem WritesIn.kfootN_trans {T N C : Set U64} {c : U64} {s s1 s2 : S} {σ σ1 : Fl4Spec.State Unit}
    (h1 : P1.WritesIn st s s1 (SFootN st T c s)) (hz : SzKeepC C σ σ1)
    (h2 : P1.WritesIn st s1 s2 (KFoot st T N C c s1 σ1)) : P1.WritesIn st s s2 (KFootN st T N C c s σ) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with (hb | hb) | hb | hb | ⟨sc, hsc, x, n, hk, ho, hne⟩
    · exact Or.inl (KFoot.of_sfoot hb)
    · exact Or.inr hb
    · exact Or.inl (KFoot.of_sfoot ((SFoot.ksb h1.1).1 hb))
    · exact Or.inl (KFoot.of_nw hb)
    · obtain ⟨x0, hk0⟩ := hz sc hsc x n hk
      exact Or.inl (KFoot.of_sw ⟨sc, hsc, x0, n, hk0, ho, hne⟩)

set_option maxHeartbeats 2000000 in
/-- **`schedule_choose_new_thread` refines l4v's, with the domain switch**:
as `schedule_choose_new_thread_refines` when the domain time is nonzero;
when it is 0, from `NdOK` (ScNextDom: `next_domain` back to entry 0 on both
sides) and `ArchNd` [P], `next_domain` then `choose_thread` at FL4's
`ndS s t` and the spec's `ndSt σa t'` (`σa` after
`arch_prepare_next_domain`). The post keeps `TK0` (not the domain time)
and widens the footprint by `NdW` (`SFootN`). -/
theorem scnt_refines0 {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSw st ar N T C c) (hAN : ArchNd st N T C c)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) :
    sched.schedule_choose_new_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.scheduleChooseNewThread (Z := Unit) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.kheap = σ.kheap ∧ TK0 σ σ' ∧
      P1.WritesIn st s r.1 (SFootN st T c s) ⦄ := by
  by_cases hd0 : σ.domainTime ≠ 0
  · refine WP.spec_mono (schedule_choose_new_thread_refines s a σ hS hR hN hI (hA.1 s a σ hS hR) (hA.2 s a σ hS hR)
      hd0) ?_
    rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, TK.tk0 h10, WritesIn.sfootN_of h11⟩
  have hnd := hdt.resolve_left hd0
  have hd0' : σ.domainTime = 0 := not_not.1 hd0
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hkf, hka⟩ := ks_fit hS
  obtain ⟨hD, hV, hidx⟩ := hnd
  obtain ⟨w24, w32, wd1, we0, hl0, hu⟩ := next_domain_words hD hV hidx
  have hNc : P1.NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  unfold sched.schedule_choose_new_thread
  step with Sched.sched.domain_time.spec2 as ⟨i, hi⟩
  have hi0 : i = 0#u64 := by
    apply UScalar.eq_of_val_eq
    have e := hs.domTime
    rw [hd0', ← hi] at e
    have := congrArg BitVec.toNat e
    simpa using this.symm
  simp only [hi0, ↓reduceIte, bind_ok]
  rw [next_domain_eq s hNc w24 w32 wd1 we0]
  simp only [bind_ok]
  set t := L.mem s (ksW (L.ksb s) (durOff 0#u64))
  -- the spec: `arch_prepare_next_domain`, then `next_domain`
  obtain ⟨σa, ha1, haS, haR, haK, hdl, hdi, hds⟩ := hAN s σ hS hR
  have hVa : DomListOK σa := hV.congr hdl hdi hds
  have hl : σa.domainList.length = 2 := by rw [hdl]; exact hD.1
  have hnx0 := nextDomain_eq (σ := σa) hl hVa (by rw [hdl]; exact hl0)
  have hnx : Fl4Spec.nextDomain (Z := Unit) σa = ({((), ndSt σa t.bv)}, False) := by rw [← hu]; exact hnx0
  set σn := ndSt σa t.bv
  have hSn : SchedRel st N T C c (ndS (L := L) s t) σn := schedRel_ndS haS t
  have hRn : NtfnStateRel N T (L.mem (ndS (L := L) s t)) σn := ntfnRel_ndS (σ' := σn) haR haS hNk rfl t
  have hNn : NSC N C σn := fun n hn x p hx hp => hN n hn x p (by rw [← haK.1]; exact hx) hp
  have hIn : Inv σn := hI.congr haK.1 haK.2.1 haK.2.2.1 haK.2.2.2.2.2.1
  refine WP.spec_mono (choose_thread_refines (ndS (L := L) s t) a σn hSn hRn hNn hIn (hA.1 _ a σn hSn hRn)
    (hA.2 _ a σn hSn hRn) (hSn.lists.choose_spec.choose_spec.2.idleTh).symm) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, ?_, h7.trans haK.2.2.2.2.1, h8.trans haK.2.2.1, h9.trans haK.1, ?_, ?_⟩
  · unfold Fl4Spec.scheduleChooseNewThread
    rw [nd_gets_bind]
    unfold Fl4Spec.NonDet.when
    rw [if_pos hd0', nd_bind_one (show (do Fl4Spec.archPrepareNextDomain; Fl4Spec.nextDomain :
      Fl4Spec.SMonad Unit Unit) σ = ({((), σn)}, False) from by rw [nd_bind_one ha1]; exact hnx), nd_bind_one h1]
    rfl
  · rcases h6 with h6 | h6
    · exact Or.inl (h6.trans haK.2.2.2.2.2.2.2.2.1)
    · exact Or.inr (by rw [← schedulable_heap (σ' := σn) haK.1 haK.2.2.1]; exact h6)
  · exact (show TK0 σ σn from ⟨haK.2.2.2.2.2.1, haK.2.2.2.2.2.2.1, haK.2.2.2.2.2.2.2.2.1, hs.curDom.1.symm,
      haK.2.2.2.2.2.2.2.2.2.2.2⟩).trans (TK.tk0 h11)
  · have hRa : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) :=
      P1.nodeAt_aligned hNc (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
    have hRv := P1.nodeAt_val hNc (off := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM])
    have hf := hNc.fits
    simp only [P1.LawfulStore.nodeBase] at hf
    have hw0 := ndS_writes (st := st) hkf hka hRa (fun o ho => by
        rw [hRv, ksW_val (by omega)]; simp only [P1.LawfulStore.nodeBase]; simp [layout.node.REPROGRAM]; omega)
      (by have := hs.curDom.2; rwa [curDomA_ks] at this) t
    refine WritesIn.sfootN_trans (hw0.mono fun b hb => ?_) (WritesIn.sfootN_of h12)
    rcases hb with hb | rfl
    · exact Or.inr hb
    · refine Or.inl (Or.inr ⟨?_, ?_⟩) <;> rw [hRv, hc.cur] <;> simp [layout.node.REPROGRAM]

end

end

end Fl4Proofs.P3
