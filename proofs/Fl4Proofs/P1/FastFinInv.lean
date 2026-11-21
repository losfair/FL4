/-
# The fault fast path's `finish` reads from the entry state (FL4 #56, m63 (d2))

m60's `FinReads` (the reads `possible_switch_to`, `schedule` and
`choose_thread` make after the fault, at the state `s15` after
`unblock_sporadic`) derived from facts at the entry state:

* `unblock_sporadic` writes only the handler's SC ring and the core's
  `REPROGRAM` word (`unblock_sporadic_fr`); with m61's `FaultKeep` this gives
  what the whole run keeps up to `s15` and past the action write
  (`FinKeep`, `finKeep15`, `FinKeep.wr_act`);
* `is_highest_prio` is a fact about the bitmap (`is_hp_unfold`,
  `is_hp_of_le`, `le_of_is_hp`), so it is re-read from `BitmapOK`;
* nothing due (`NoDue`) and the ready queues (`ReadyQueues`) are re-read
  word by word (`NoDue.agree`, `ReadyQueues.keep`);
* `set_vm_root`'s reads (`VmOff`) need the ASID table and its pools placed
  among the other kernel objects: `AsidOff` [J].
-/
import Fl4Proofs.P1.FastFaultInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## `is_highest_prio` from the bitmap -/

theorem is_hp_unfold (s : S) (dom p : U64) : sched.is_highest_prio st s dom p =
    (if L.l1W s (L.cpu s) = 0#u64 then ok true else do let q ← sched.highest_prio st s dom; ok (p >= q)) := by
  unfold sched.is_highest_prio
  rw [bitmap_dom_one]; simp only [bind_ok]
  rw [L.cur_cpu_eq]; simp only [bind_ok]
  rw [eq_of_spec_fd l1_off_zero]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s _ _)]; simp only [bind_ok]
  rfl

/-- `is_highest_prio p` holds at any state whose bitmap marks no priority
above `p`. -/
theorem is_hp_of_le {T : Set U64} {Y : S} {NE : U64 → Prop} {p : U64} (dom : U64)
    (hN : NodePlaced st T Y (L.cpu Y)) (hB : BitmapOK st Y (L.cpu Y) NE)
    (hle : ∀ p' : U64, p'.val < 256 → NE p' → p'.val ≤ p.val) :
    sched.is_highest_prio st Y dom p = ok true := by
  rw [is_hp_unfold]
  by_cases h0 : L.l1W Y (L.cpu Y) = 0#u64
  · rw [if_pos h0]
  rw [if_neg h0]
  obtain ⟨q, hq, hq1, hq2, -⟩ := spec_ex_fd (sched.highest_prio.spec (T := T) Y dom NE hN hB h0)
  rw [hq]; simp only [bind_ok]
  have := hle q hq1 hq2
  congr 1
  simp only [ge_iff_le, decide_eq_true_eq]
  exact this

/-- An accepted `is_highest_prio p` bounds every priority the bitmap marks. -/
theorem le_of_is_hp {T : Set U64} {s : S} {NE : U64 → Prop} {dom p : U64}
    (hN : NodePlaced st T s (L.cpu s)) (hB : BitmapOK st s (L.cpu s) NE)
    (h : sched.is_highest_prio st s dom p = ok true) :
    ∀ p' : U64, p'.val < 256 → NE p' → p'.val ≤ p.val := by
  intro p' hp' hne
  have hl2 := (hB.l2 p' hp').2 hne
  have hw : L.l2W s (L.cpu s) (p'.val / 64) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hl2⟩
  have hl1b := (hB.l1 (p'.val / 64) (by omega)).2 ⟨by omega, hw⟩
  have hl1ne : L.l1W s (L.cpu s) ≠ 0#u64 := by
    intro e; rw [e] at hl1b; simp at hl1b
  obtain ⟨q, hq, hq1, -, hq3⟩ := spec_ex_fd (sched.highest_prio.spec (T := T) s dom NE hN hB hl1ne)
  rw [is_hp_unfold, if_neg hl1ne, hq] at h
  simp only [bind_ok] at h
  have hqp : q ≤ p := by
    have := ok_inj_ff h
    simpa using this
  have := hq3 p' hp' hne
  have hqp' : q.val ≤ p.val := hqp
  omega

/-! ## What `unblock_sporadic` writes -/

theorem unblock_sporadic_fr {X s15 : S} {d : obj.Tcb} {A : U64} {sb : Nat} (h : UsOff (L := L) X d A sb)
    (e : endpoint.unblock_sporadic st X d = ok s15) :
    WritesIn st X s15 (fun b => InRing (L.mem X (scA d)) sb b ∨ b = L.nodeA X layout.node.REPROGRAM) := by
  unfold endpoint.unblock_sporadic at e
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) X d)] at e
  simp only [bind_ok, bind_tc_ok] at e
  rw [sc_sporadic_eq] at e; simp only [bind_ok, bind_tc_ok] at e
  by_cases h0 : L.mem X (scA d) = 0#u64
  · simp only [h0, ↓reduceIte, Bool.false_eq_true, bind_ok, bind_tc_ok] at e
    obtain rfl := ok_inj_ff e
    exact WritesIn.refl _ _
  simp only [h0, ↓reduceIte] at e
  by_cases h1 : (L.mem X (sporA (L.mem X (scA d))) != 0#u64) = true
  swap
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, bind_ok, bind_tc_ok] at e
    obtain rfl := ok_inj_ff e
    exact WritesIn.refl _ _
  have hW := h.wf h0 (bne_iff_ne.1 h1)
  simp only [h1, ↓reduceIte] at e
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at e
  simp only [bind_ok, bind_tc_ok] at e
  obtain ⟨b1, hb1, -⟩ := spec_ex_fd (sc_ne.spec (L.mem X (scA d)) (L.mem X (L.nodeA X layout.node.CUR_SC)))
  rw [hb1] at e; simp only [bind_ok, bind_tc_ok] at e
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at e
    obtain rfl := ok_inj_ff e
    exact WritesIn.refl _ _
  · simp only [↓reduceIte] at e
    have := sporadic.unblock_check.fr hW h.rp
    rw [e, WP.spec_ok] at this; exact this

/-! ## What the fault run keeps up to `s15` and past the action write -/

/-- **What the general fault path keeps from the entry state `s` to `Y`**
(`s15` after `unblock_sporadic`, or `s15` with the action set): the node words
but `SCHED_ACTION` / `REPROGRAM`, the TCB words above the user context but the
state / reply / fault / Ep-link words, the `Ω` words but the reply's TCB word
and the handler's SC ring. -/
structure FinKeep (T Ω : Set U64) (s Y : S) (r dsc : U64) (sb : Nat) : Prop where
  ksb : L.ksb Y = L.ksb s
  cpu : L.cpu Y = L.cpu s
  node : ∀ off : U64, off.val < 4288 → off.val % 8 = 0 → off.val ≠ 16 → off.val ≠ 56 →
    L.mem Y (L.nodeAt s (L.cpu s) off) = L.mem s (L.nodeAt s (L.cpu s) off)
  tcb : ∀ y ∈ T, ∀ K : U64, 3328 < K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3360 → K.val ≠ 3376 →
    K.val ≠ 3384 → K.val ≠ 3392 → K.val ≠ 3400 → K.val ≠ 3496 → K.val ≠ 3504 →
    L.mem Y (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)
  omg : ∀ b ∈ Ω, b ≠ rTcbA r → ¬ InRing dsc sb b → L.mem Y b = L.mem s b

/-- **`FinKeep` at `s15`** from m61's `FaultKeep` at `fS14` and the footprint
of `unblock_sporadic` (the handler's SC words are `Ω` words). -/
theorem finKeep15 {T Cs Ω : Set U64} {s X s15 : S} {r dsc : U64} {sb : Nat}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs)
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (K : FaultKeep (L := L) T Ω s X r)
    (scW : ∀ b, Aligned b → InSC dsc sb b → b ∈ Ω)
    (w : WritesIn st X s15 (fun b => InRing dsc sb b ∨ b = L.nodeA X layout.node.REPROGRAM)) :
    FinKeep (L := L) T Ω s s15 r dsc sb := by
  have eR : L.nodeA X layout.node.REPROGRAM = L.nodeAt s (L.cpu s) layout.node.REPROGRAM := by
    unfold LawfulStore.nodeA; rw [K.cpu, nodeAt_of_ksb K.ksb]
  have vR : (L.nodeAt s (L.cpu s) layout.node.REPROGRAM).val = L.nodeBase s (L.cpu s) + 56 := by
    rw [nodeAt_val hN (by simp [layout.node.REPROGRAM])]; simp [layout.node.REPROGRAM]
  -- an `Ω` word or a TCB / node word is no ring word
  have nR : ∀ b, Aligned b → (∀ a ∈ Ω, a ≠ b) → ¬ InRing dsc sb b := fun b hb hn hr =>
    hn b (scW b hb hr.inSC) rfl
  refine ⟨w.1.trans K.ksb, w.2.1.trans K.cpu, ?_, ?_, ?_⟩
  · intro off ho h8 h16 h56
    have vb := nodeAt_val hN ho
    have hba := nodeAt_aligned hN ho h8
    rw [w.2.2 _ hba ?_]
    · exact K.node off ho h8
    rintro (hr | hr)
    · refine nR _ hba (fun a ha e => ?_) hr
      have := (hΩ a ha).2.2 _ hcC; rw [e, vb] at this; omega
    · rw [eR] at hr; have := congrArg UScalar.val hr; rw [vb, vR] at this; omega
  · intro y hy K' h1 h2 h3 k1 k2 k3 k4 k5 k6 k7
    have hy' := hT y hy
    have vb := tcb_wadd_val hy' h2
    have ya := hy'.align
    have hba : Aligned (core.num.U64.wrapping_add y K') := by show _ % 8 = 0; rw [vb]; omega
    rw [w.2.2 _ hba ?_]
    · exact K.tcb y hy K' h1 h2 h3 k1 k2 k3 k4 k5 k6 k7
    rintro (hr | hr)
    · refine nR _ hba (fun a ha e => ?_) hr
      have := (hΩ a ha).2.1 y hy; rw [e, vb] at this; omega
    · rw [eR] at hr; have := congrArg UScalar.val hr; rw [vb, vR] at this
      have := hN.disj y hy; omega
  · intro b hb hbr hin
    have hba := (hΩ b hb).1
    rw [w.2.2 _ hba ?_]
    · exact K.omg b hb hbr
    rintro (hr | hr)
    · exact hin hr
    · rw [eR] at hr; have := (hΩ b hb).2.2 _ hcC; rw [hr, vR] at this; omega

/-- `FinKeep` past a write to the action word. -/
theorem FinKeep.wr_act {T Cs Ω : Set U64} {s Y : S} {r dsc : U64} {sb : Nat} {v : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs)
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (K : FinKeep (L := L) T Ω s Y r dsc sb) :
    FinKeep (L := L) T Ω s (L.wr Y (actA (L := L) Y) v) r dsc sb := by
  have eA : actA (L := L) Y = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION := by
    show L.nodeAt Y (L.cpu Y) _ = _; rw [K.cpu, nodeAt_of_ksb K.ksb]
  have vA : (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val = L.nodeBase s (L.cpu s) + 16 := by
    rw [nodeAt_val hN (by simp [layout.node.SCHED_ACTION])]; simp [layout.node.SCHED_ACTION]
  have aA : Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  rw [eA]
  refine ⟨by rw [L.ksb_wr]; exact K.ksb, by rw [L.cpu_wr]; exact K.cpu, ?_, ?_, ?_⟩
  · intro off ho h8 h16 h56
    have vb := nodeAt_val hN ho
    rw [L.mem_wr_ne aA (nodeAt_aligned hN ho h8) (by rw [vA, vb]; omega)]
    exact K.node off ho h8 h16 h56
  · intro y hy K' h1 h2 h3 k1 k2 k3 k4 k5 k6 k7
    have hy' := hT y hy
    have vb := tcb_wadd_val hy' h2
    have ya := hy'.align
    have := hN.disj y hy
    rw [L.mem_wr_ne aA (by show _ % 8 = 0; rw [vb]; omega) (by rw [vA, vb]; omega)]
    exact K.tcb y hy K' h1 h2 h3 k1 k2 k3 k4 k5 k6 k7
  · intro b hb hbr hin
    have := (hΩ b hb).2.2 _ hcC
    rw [L.mem_wr_ne aA (hΩ b hb).1 (by rw [vA]; omega)]
    exact K.omg b hb hbr hin

/-- `FinKeep`'s TCB clause at the offsets the scheduler reads. -/
theorem FinKeep.tw {T Ω : Set U64} {s Y : S} {r dsc : U64} {sb : Nat} (K : FinKeep (L := L) T Ω s Y r dsc sb)
    {y : U64} (hy : y ∈ T) (Kv : U64)
    (hK : Kv.val = 3432 ∨ Kv.val = 3448 ∨ Kv.val = 3464 ∨ Kv.val = 3480 ∨ Kv.val = 3488 ∨ Kv.val = 3520 ∨
      Kv.val = 3528 ∨ Kv.val = 3592) :
    L.mem Y (core.num.U64.wrapping_add y Kv) = L.mem s (core.num.U64.wrapping_add y Kv) :=
  K.tcb y hy Kv (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem getLastD_mem_cons {α : Type _} (x : α) (xs : List α) (d : α) : (x :: xs).getLastD d ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp [List.getLastD]
  | cons y ys ih => exact List.mem_cons_of_mem _ (ih y)

/-! ## Re-reading `NoDue` and the ready queues -/

/-- **`NoDue` only reads seven words.** -/
theorem NoDue.agree {s Y : S} (h : NoDue (L := L) s) (hk : L.ksb Y = L.ksb s) (hc : L.cpu Y = L.cpu s)
    (eTM : L.mem Y (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (eCT : L.mem Y (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME))
    (eTD : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem Y (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) =
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (eRH : L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))
    (eSC : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      L.mem Y (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) =
        L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
    (eHD : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      L.mem Y (headA (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))) =
        L.mem s (headA (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))))
    (eRT : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      L.mem Y (rtA (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
        (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))) =
      L.mem s (rtA (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
        (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))))) :
    NoDue (L := L) Y := by
  have eN : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o := fun o => by rw [hc, nodeAt_of_ksb hk]
  obtain ⟨h1, h2⟩ := h
  unfold NoDue
  simp only [LawfulStore.curTime, LawfulStore.nodeA, LawfulStore.refill, LawfulStore.rhead] at h2 ⊢
  simp only [eN]
  rw [eTM, eCT, eRH]
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1
    · exact Or.inl h1
    · by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
      · exact Or.inl h0
      · right; rw [eTD h0]; exact h1
  · rcases h2 with h2 | h2
    · exact Or.inl h2
    · by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64
      · exact Or.inl h0
      · right
        have e2 := eHD h0
        unfold LawfulStore.rhead at eRT
        rw [eSC h0, e2, eRT h0]; exact h2

/-- **The ready queues at a state that keeps the queue words, the members'
scheduler links and the bitmap.** -/
theorem ReadyQueues.keep {T Ω : Set U64} {s Y : S} {r dsc : U64} {sb : Nat} {Q : U64 → List U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (h : ReadyQueues st T s (L.cpu s) Q)
    (K : FinKeep (L := L) T Ω s Y r dsc sb) : ReadyQueues st T Y (L.cpu Y) Q := by
  rw [K.cpu]
  have eN : ∀ o, L.nodeAt Y (L.cpu s) o = L.nodeAt s (L.cpu s) o := fun o => nodeAt_of_ksb K.ksb _ _
  refine ⟨ReadyRel.agree h.1 (fun p hp => ?_) (fun p hp y hy => ?_), BitmapOK.agree h.2 ?_ (fun g hg => ?_)⟩
  · unfold LawfulStore.rqQ
    rw [eN, eN, K.node _ (by rw [rqOff_val hp] <;> omega) (by rw [rqOff_val hp] <;> omega)
        (by rw [rqOff_val hp] <;> omega) (by rw [rqOff_val hp] <;> omega),
      K.node _ (by rw [rqTailOff_val hp] <;> omega) (by rw [rqTailOff_val hp] <;> omega)
        (by rw [rqTailOff_val hp] <;> omega) (by rw [rqTailOff_val hp] <;> omega)]
  · have hyT := (h.1.rel p hp).mem y hy
    exact ⟨K.tcb y hyT 3480#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      K.tcb y hyT 3488#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)⟩
  · unfold LawfulStore.l1W
    rw [eN, K.node _ (by rw [l1Off_val] <;> omega) (by rw [l1Off_val] <;> omega) (by rw [l1Off_val] <;> omega)
      (by rw [l1Off_val] <;> omega)]
  · unfold LawfulStore.l2W
    rw [eN, K.node _ (by rw [l2Off_val hg] <;> omega) (by rw [l2Off_val hg] <;> omega) (by rw [l2Off_val hg] <;> omega)
      (by rw [l2Off_val hg] <;> omega)]

end

/-! ## `set_vm_root`'s reads: the ASID table and pools -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **[J] The ASID table and its pools lie among the other kernel objects**
(`Ω`, outside the TCBs and nodes) and hold no frame word (`Sg`: SC, reply and
notification words): the table words `find_asid` reads (`hi < 2048`) and,
for a nonzero entry, the pool words (`lo < 512`). l4v counterpart:
`valid_global_objs` / `valid_asid_table` (the table is kernel-global state,
each entry an `ASIDPool` object) with `pspace_distinct` (an ASID pool is
disjoint from every TCB, SC, reply and notification object). Why a premise:
P1 places no ASID object (P3 `VsRel.tmem` / `pool` does, through the state
relation); it is the same placement Hyps4's `aset` assumes for MakePool's
table write (`set_asid_table` writes `Ω \ Sg` words). -/
def AsidOff (Ω Sg : Set U64) (s : S) : Prop :=
  ∀ hi : U64, hi.val < 2048 → atAF (L.ksb s) hi ∈ Ω ∧ atAF (L.ksb s) hi ∉ Sg ∧
    (L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
      peAF (L.mem s (atAF (L.ksb s) hi)) lo ∈ Ω ∧ peAF (L.mem s (atAF (L.ksb s) hi)) lo ∉ Sg)

theorem vtA_val {t : U64} (h : TcbAddr t) : (vtA t).val = t.val + 32 := by
  have := h.fits
  unfold vtA layout.tcb.SLOT_VTABLE layout.cte.SIZE
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  all_goals omega

/-- A node word or a TCB word above the user context (what the general path
writes after the fault, before `set_vm_root`). -/
def NodeOrTcb (T : Set U64) (s : S) (w : U64) : Prop :=
  (∃ off : U64, off.val < 4288 ∧ w = L.nodeAt s (L.cpu s) off) ∨
    (∃ y ∈ T, ∃ K : U64, 3328 ≤ K.val ∧ K.val < 4096 ∧ w = core.num.U64.wrapping_add y K)

/-- **`set_vm_root d` does not read a node word or a TCB word above the user
context**, at a state that keeps the entry state's `Ω` words outside the
frame words (`FinKeep`), given the ASID placement `AsidOff`. -/
theorem vmOff_of {T Cs Ω Sg : Set U64} {s U : S} {r dsc : U64} {sb : Nat} {d w : U64}
    (hT : TcbPlaced T) (hd : d ∈ T) (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs)
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a)
    (hksΩ : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add (L.ksb s) o ∈ Ω)
    (hrS : rTcbA r ∈ Sg) (scSg : ∀ b, Aligned b → InSC dsc sb b → b ∈ Sg)
    (hA : AsidOff (L := L) Ω Sg s) (K : FinKeep (L := L) T Ω s U r dsc sb)
    (hw : Aligned w) (hwo : NodeOrTcb (L := L) T s w) : VmOff (L := L) U d w := by
  have hne : ∀ a ∈ Ω, w ≠ a := by
    intro a ha e
    obtain ⟨-, hoT, hoN⟩ := hΩ a ha
    rcases hwo with ⟨off, ho, rfl⟩ | ⟨y, hy, K', h1, h2, rfl⟩
    · have := hoN _ hcC; rw [← e, nodeAt_val hN ho] at this; omega
    · have := hoT y hy; rw [← e, tcb_wadd_val (hT y hy) h2] at this; omega
  have hd' := hT d hd
  have da := hd'.align; have df := hd'.fits
  have nsl : ∀ k : Nat, k < 3328 → w.val ≠ d.val + k := by
    intro k hk e
    rcases hwo with ⟨off, ho, rfl⟩ | ⟨y, hy, K', h1, h2, rfl⟩
    · have := hN.disj d hd; rw [nodeAt_val hN ho] at e; omega
    · have hy' := hT y hy; have ya := hy'.align; rw [tcb_wadd_val hy' h2] at e; omega
  have vs1 : (core.num.U64.wrapping_add (vtA d) 8#u64).val = d.val + 40 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vtA_val hd']; omega
  have eTab : ∀ hi : U64, hi.val < 2048 → L.mem U (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) := by
    intro hi hhi
    obtain ⟨h1, h2, -⟩ := hA hi hhi
    exact K.omg _ h1 (fun e => h2 (e ▸ hrS)) (fun hin => h2 (scSg _ (hΩ _ h1).1 hin.inSC))
  refine ⟨hw, ⟨by show _ % 8 = 0; rw [vtA_val hd']; omega, fun e => nsl 32 (by omega) (by rw [e, vtA_val hd'])⟩,
    ⟨by show _ % 8 = 0; rw [vs1]; omega, fun e => nsl 40 (by omega) (by rw [e, vs1])⟩, ?_, ?_⟩
  · have hk : krA (L := L) U = core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT := by
      unfold krA; rw [K.ksb]
    rw [hk]
    have hm := hksΩ layout.ks.KERNEL_ROOT (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    exact ⟨(hΩ _ hm).1, hne _ hm⟩
  · intro hi hhi
    rw [K.ksb]
    obtain ⟨h1, -, h3⟩ := hA hi hhi
    refine ⟨⟨(hΩ _ h1).1, hne _ h1⟩, fun lo hlo hz => ?_⟩
    rw [eTab hi hhi] at hz ⊢
    obtain ⟨p1, -⟩ := h3 hz lo hlo
    exact ⟨(hΩ _ p1).1, hne _ p1⟩

/-! ## The words `enqueue` writes -/

/-- A word `enqueue` / `dequeue` may write: a node word at or above the
bitmap (offset ≥ 128) or a TCB's scheduler link / in-queues word. -/
def QW (T : Set U64) (s : S) (w : U64) : Prop :=
  (∃ off : U64, off.val < 4288 ∧ off.val % 8 = 0 ∧ 128 ≤ off.val ∧ w = L.nodeAt s (L.cpu s) off) ∨
    (∃ y ∈ T, ∃ K : U64, (K.val = 3480 ∨ K.val = 3488 ∨ K.val = 3592) ∧ w = core.num.U64.wrapping_add y K)

section qw
variable {T Cs Ω : Set U64} {s : S} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
include hT hN

theorem QW.aligned {w : U64} (h : QW (L := L) T s w) : Aligned w := by
  rcases h with ⟨off, ho, h8, -, rfl⟩ | ⟨y, hy, K, hK, rfl⟩
  · exact nodeAt_aligned hN ho h8
  · have hy' := hT y hy; have := hy'.align
    show _ % 8 = 0; rw [tcb_wadd_val hy' (by omega)]; omega

theorem QW.ne_node {w off : U64} (h : QW (L := L) T s w) (ho : off.val < 128) :
    w ≠ L.nodeAt s (L.cpu s) off := by
  intro e; have e' := congrArg UScalar.val e
  rw [nodeAt_val hN (by omega)] at e'
  rcases h with ⟨off', ho', -, h1, rfl⟩ | ⟨y, hy, K, hK, rfl⟩
  · rw [nodeAt_val hN ho'] at e'; omega
  · have hy' := hT y hy; rw [tcb_wadd_val hy' (by omega)] at e'; have := hN.disj y hy; omega

theorem QW.ne_tcb {w y K : U64} (h : QW (L := L) T s w) (hy : y ∈ T) (hK : K.val < 4096)
    (h1 : K.val ≠ 3480) (h2 : K.val ≠ 3488) (h3 : K.val ≠ 3592) :
    w ≠ core.num.U64.wrapping_add y K := by
  intro e; have e' := congrArg UScalar.val e
  have hy' := hT y hy; have ya := hy'.align
  rw [tcb_wadd_val hy' hK] at e'
  rcases h with ⟨off', ho', -, -, rfl⟩ | ⟨z, hz, K', hK', rfl⟩
  · rw [nodeAt_val hN ho'] at e'; have := hN.disj y hy; omega
  · have hz' := hT z hz; have za := hz'.align; rw [tcb_wadd_val hz' (by omega)] at e'; omega

theorem QW.ne_omg (hcC : L.cpu s ∈ Cs) {w a : U64} (h : QW (L := L) T s w) (ha : OutsideObjs st T Cs s a) :
    w ≠ a := by
  intro e; subst e
  obtain ⟨-, hoT, hoN⟩ := ha
  rcases h with ⟨off', ho', -, -, rfl⟩ | ⟨z, hz, K', hK', rfl⟩
  · have := hoN _ hcC; rw [nodeAt_val hN ho'] at this; omega
  · have hz' := hT z hz; have := hoT z hz; rw [tcb_wadd_val hz' (by omega)] at this; omega

theorem QW.nodeOrTcb {w : U64} (h : QW (L := L) T s w) : NodeOrTcb (L := L) T s w := by
  rcases h with ⟨off, ho, -, -, rfl⟩ | ⟨y, hy, K, hK, rfl⟩
  · exact Or.inl ⟨off, ho, rfl⟩
  · exact Or.inr ⟨y, hy, K, by omega, by omega, rfl⟩

end qw

theorem qw_nodeAt {T : Set U64} {s Y : S} {off : U64} (hk : L.ksb Y = L.ksb s) (hc : L.cpu Y = L.cpu s)
    (ho : off.val < 4288) (h8 : off.val % 8 = 0) (h1 : 128 ≤ off.val) : QW (L := L) T s (L.nodeAt Y (L.cpu Y) off) :=
  Or.inl ⟨off, ho, h8, h1, by rw [hc, nodeAt_of_ksb hk]⟩

theorem qw_next {T : Set U64} {s : S} {y : U64} (hy : y ∈ T) : QW (L := L) T s (nextA .Sched y) :=
  Or.inr ⟨y, hy, 3480#u64, by decide, rfl⟩
theorem qw_prev {T : Set U64} {s : S} {y : U64} (hy : y ∈ T) : QW (L := L) T s (prevA .Sched y) :=
  Or.inr ⟨y, hy, 3488#u64, by decide, rfl⟩
theorem qw_inq {T : Set U64} {s : S} {y : U64} (hy : y ∈ T) : QW (L := L) T s (inqA y) :=
  Or.inr ⟨y, hy, 3592#u64, by decide, rfl⟩

/-- A read past `enqueue`'s writes. -/
theorem mem_wrs_qw {T : Set U64} {s X : S} {b : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (hb : Aligned b) (hne : ∀ w, QW (L := L) T s w → w ≠ b) (lW : List (U64 × U64))
    (hl : ∀ x ∈ lW, QW (L := L) T s x.1) : L.mem (wrs (L := L) X lW) b = L.mem X b :=
  mem_wrs_ne hb lW X fun x hx => ⟨(hl x hx).aligned hT hN, hne _ (hl x hx)⟩


/-! ## Nothing due, past the enqueue -/

/-- **`NoDue` at the enqueued state** from `NoDue` at the entry state: the
earliest timer is null or a TCB (`TimerOK.min`), the release head's SC is
well formed and its words are kept (`rel_head`). -/
theorem noDue_wrs {T Cs Ω : Set U64} {s X : S} {r dsc : U64} {sb : Nat}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs)
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (KX : FinKeep (L := L) T Ω s X r dsc sb) (hND : NoDue (L := L) s)
    (hTM : Tz T (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (hRel : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ∈ T ∧
      ∃ zc, RefillsWF st s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))) zc ∧
        ∀ b, Aligned b → InSC (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))) zc b →
          b ∈ Ω ∧ b ≠ rTcbA r ∧ ¬ InRing dsc sb b)
    (lW : List (U64 × U64)) (hl : ∀ x ∈ lW, QW (L := L) T s x.1) : NoDue (L := L) (wrs (L := L) X lW) := by
  have mN : ∀ o : U64, o.val < 128 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 →
      L.mem (wrs (L := L) X lW) (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 h3 h4 => by
    rw [mem_wrs_qw hT hN (nodeAt_aligned hN (by omega) h2) (fun w hw => hw.ne_node hT hN h1) lW hl]
    exact KX.node o (by omega) h2 h3 h4
  have mT : ∀ y ∈ T, ∀ K : U64, (K.val = 3464 ∨ K.val = 3528) →
      L.mem (wrs (L := L) X lW) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK
    have hy' := hT y hy
    have ya := hy'.align
    rw [mem_wrs_qw hT hN (by show _ % 8 = 0; rw [tcb_wadd_val hy' (by omega)]; omega)
      (fun w hw => hw.ne_tcb hT hN hy (by omega) (by omega) (by omega) (by omega)) lW hl]
    exact KX.tcb y hy K (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have mO : ∀ b ∈ Ω, b ≠ rTcbA r → ¬ InRing dsc sb b → L.mem (wrs (L := L) X lW) b = L.mem s b :=
    fun b hb h1 h2 => by
      rw [mem_wrs_qw hT hN (hΩ b hb).1 (fun w hw => hw.ne_omg hT hN hcC (hΩ b hb)) lW hl]
      exact KX.omg b hb h1 h2
  refine NoDue.agree hND (by rw [ksb_wrs, KX.ksb]) (by rw [cpu_wrs, KX.cpu])
    (mN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]))
    (mN _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])) ?_
    (mN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) ?_ ?_ ?_
  · intro h0
    rcases hTM with h | h
    · exact absurd h h0
    · exact mT _ h 3528#u64 (Or.inr (by decide))
  · intro h0; exact mT _ (hRel h0).1 3464#u64 (Or.inl (by decide))
  · intro h0
    obtain ⟨-, zc, hW, hin⟩ := hRel h0
    obtain ⟨h8, -, -⟩ := hW.bounds
    obtain ⟨h96, -, -, hh, -, -⟩ := hW.inside
    have hb : Aligned (headA (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))) := by
      show _ % 8 = 0; rw [hh]; omega
    obtain ⟨a1, a2, a3⟩ := hin _ hb ⟨by rw [hh]; omega, by rw [hh]; omega⟩
    exact mO _ a1 a2 a3
  · intro h0
    obtain ⟨-, zc, hW, hin⟩ := hRel h0
    obtain ⟨h8, -, -⟩ := hW.bounds
    obtain ⟨-, -, -, -, -, hi⟩ := hW.inside
    obtain ⟨e1, e2, e3⟩ := hi _ hW.head_lt
    have hb : Aligned (rtA (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
        (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))) := by
      show _ % 8 = 0; rw [e1]; omega
    obtain ⟨a1, a2, a3⟩ := hin _ hb ⟨by rw [e1]; omega, by rw [e1]; omega⟩
    exact mO _ a1 a2 a3

end

/-! ## The release head's SC (F4) -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **The release queue's head is a TCB whose SC is well formed and lies
apart from the reply object and from the handler's SC** (F4: the handler is
not released, and an SC names its TCB back, `ScExtra0.bound`). -/
theorem rel_head {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} {s : S} {dest r : U64}
    (hSQ : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX0 : ScExtra0 st T Cs Scs Nt s) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hr : r ∈ Rp)
    (hdT : dest ∈ T) (hsc : L.mem s (scA dest) ≠ 0#u64)
    (hnr : (L.mem s (inqA dest) &&& sched.Q_RELEASE) = 0#u64)
    (h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64) :
    L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ∈ T ∧
      ∃ zc, RefillsWF st s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))) zc ∧
        ∀ b, Aligned b → InSC (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))) zc b →
          b ∈ Ω ∧ b ≠ rTcbA r ∧ ¬ InRing (L.mem s (scA dest)) (Z (L.mem s (scA dest))) b := by
  have hq := hSQ.release _ hSQ.cur
  have hhd : (R (L.cpu s)).headD 0#u64 = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := hq.head.symm
  have hmem : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ∈ R (L.cpu s) := by
    rw [← hhd]
    cases e : R (L.cpu s) with
    | nil => rw [e] at hhd; exact absurd hhd.symm h0
    | cons x xs => simp
  have hrT := hq.mem _ hmem
  have haff := hSQ.inR _ hSQ.cur _ hmem
  have hrel := (hSQ.released _ hrT).2 (by rw [haff]; exact hmem)
  have hsc0 := hB.r _ hrT hrel
  have hact := hB.sact _ hrT (Or.inr (Or.inl hrel)) hsc0
  obtain ⟨hcS, hback, -⟩ := hX0.bound _ hrT hsc0
  have hdsc := (hX0.bound dest hdT hsc).1
  have hWF := (hS.all _ hcS).1 ((hS.act _ hcS).1 hact)
  refine ⟨hrT, _, hWF, fun b hb hin => ⟨hS.sub _ ((hS.all _ hcS).2.2 b hb hin), ?_, ?_⟩⟩
  · intro e
    have := hO.rpSc r hr _ hcS
    rw [e] at hin
    unfold InSC at hin; rw [rTcbA_val0] at hin; omega
  · intro hR
    have hne : L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) ≠ L.mem s (scA dest) := by
      intro e
      obtain ⟨-, hb2, -⟩ := hX0.bound dest hdT hsc
      rw [← e, hback] at hb2
      rw [hb2] at hrel; exact hrel hnr
    have := hO.scDisj _ hcS _ hdsc hne
    unfold InRing at hR; unfold InSC at hin; omega


/-! ## (d2) `FinReads` at `s15` from the entry state -/

set_option maxHeartbeats 1600000 in
/-- **(d2) m60's `FinReads` at `s15`** (after `unblock_sporadic` at the
meeting state `fS14`), from facts at the entry state `s`: m61's `FaultEnt`,
what `schedulable_here` and `is_highest_prio` checked (`HereF`, `hhi`), the
P1 invariants `SchedQueuesInv` / `BoundInv` / `SCsOK` / `ScExtra0` /
`ObjsOK` with the reply `r ∈ Rp`, the run's keep facts to `fS14` (m61
`FaultKeep`, the current thread blocked on the reply) and the ASID placement
`AsidOff` [J]. -/
theorem finReads_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} {s S8 s15 : S} {t : obj.Tcb} {ptr dest r : U64}
    {rest : List U64}
    (E : FaultEnt (L := L) T Cs Ω U s t ptr dest r rest) (HF : HereF (L := L) s dest)
    (hhi : sched.is_highest_prio st s 0#u64 (L.mem s (prioA dest)) = ok true)
    (hSQ : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX0 : ScExtra0 st T Cs Scs Nt s) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hr : r ∈ Rp)
    (hA : AsidOff (L := L) Ω Sg s)
    (K : FaultKeep (L := L) T Ω s (fS14 (L := L) S8 t dest r) r)
    (hst : L.mem (fS14 (L := L) S8 t dest r) (stA t) = sched.TS_BLOCKED_ON_REPLY)
    (h15 : endpoint.unblock_sporadic st (fS14 (L := L) S8 t dest r) dest = ok s15) :
    actA (L := L) s15 = actA (L := L) (fS14 (L := L) S8 t dest r) ∧ FinReads (L := L) s15 dest := by
  have hT := E.hT
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hd' := hT dest hdT
  have htT := E.ht
  have ht' := hT t htT
  have hN := E.hN
  have hcC := E.hcC
  have hΩ := E.hΩ
  -- the handler's SC
  have hdsc : L.mem s (scA dest) ∈ Scs := (hX0.bound dest hdT HF.sc).1
  obtain ⟨hPl, hZ7⟩ := hO.sc _ hdsc
  have scSg : ∀ b, Aligned b → InSC (L.mem s (scA dest)) (Z (L.mem s (scA dest))) b → b ∈ Sg :=
    (hS.all _ hdsc).2.2
  have scW : ∀ b, Aligned b → InSC (L.mem s (scA dest)) (Z (L.mem s (scA dest))) b → b ∈ Ω :=
    fun b hb h => hS.sub _ (scSg b hb h)
  have spWF : L.mem s (sporA (L.mem s (scA dest))) ≠ 0#u64 →
      RefillsWF st s (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    fun h => (hS.all _ hdsc).1 ((hS.act _ hdsc).1 (hS.spor _ hdsc h))
  have hU := usOff_of E K scW (hS.sub _ (hS.spSg _ hdsc)) spWF (hO.rpSc r hr _ hdsc) hZ7 hPl.fits
  have w15 := unblock_sporadic_fr hU h15
  have esc14 : L.mem (fS14 (L := L) S8 t dest r) (scA dest) = L.mem s (scA dest) :=
    K.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  rw [esc14] at w15
  have K15 := finKeep15 hT hN hcC hΩ K scW w15
  have hA15 : actA (L := L) s15 = actA (L := L) (fS14 (L := L) S8 t dest r) := actA_of w15.1 w15.2.1
  refine ⟨hA15, ?_⟩
  have KX0 := K15.wr_act (v := sched.ACTION_CHOOSE_NEW) hT hN hcC hΩ
  unfold FinReads
  obtain ⟨X, hXd⟩ : ∃ X, X = L.wr s15 (actA (L := L) s15) sched.ACTION_CHOOSE_NEW := ⟨_, rfl⟩
  rw [← hXd] at KX0 ⊢
  have KX := KX0
  clear KX0
  -- frame words and addresses
  have hrS : rTcbA r ∈ Sg := by
    have := (hO.rp r hr).1
    exact hO.rpW r hr _ (by show _ % 8 = 0; rw [rTcbA_val0]; omega) (by rw [rTcbA_val0] <;> omega)
      (by rw [rTcbA_val0]; omega)
  have eNX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [KX.cpu, nodeAt_of_ksb KX.ksb]
  have eNU : ∀ o, L.nodeAt s15 (L.cpu s15) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [K15.cpu, nodeAt_of_ksb K15.ksb]
  have hNX : NodePlaced st T X (L.cpu X) := by rw [KX.cpu]; exact hN.ksb KX.ksb
  have ksv : ∀ o : U64, o.val < 13568 →
      (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
    intro o ho
    have := hN.fits
    simp only [LawfulStore.nodeBase] at this
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have ksK : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
      L.mem X (core.num.U64.wrapping_add (L.ksb X) o) = L.mem s (core.num.U64.wrapping_add (L.ksb s) o) := by
    intro o h1 h2
    rw [KX.ksb]
    have hm := hS.ksΩ o h1 h2
    refine KX.omg _ hm (fun e => ?_) (fun hin => ?_)
    · have := hS.ks _ hrS; rw [← e, ksv o h1] at this; omega
    · have hsg := scSg _ (hΩ _ hm).1 hin.inSC
      have := hS.ks _ hsg; rw [ksv o h1] at this; omega
  have vst : (stA t).val = t.val + 3328 := by rw [stA_eq]; exact tcb_wadd_val ht' (by decide)
  have aS : Aligned (stA t) := by show _ % 8 = 0; rw [vst]; have := ht'.align; omega
  have hcur : L.mem X (curA (L := L) X) = t := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) = t
    rw [eNX, KX.node _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]
    exact E.hcur
  have hstX : L.mem X (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    have vA : (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val = L.nodeBase s (L.cpu s) + 16 := by
      rw [nodeAt_val hN (by simp [layout.node.SCHED_ACTION])]; simp [layout.node.SCHED_ACTION]
    have nd := hN.disj t htT
    have ta := ht'.align
    rw [hXd]
    show L.mem (L.wr s15 (L.nodeAt s15 (L.cpu s15) layout.node.SCHED_ACTION) _) _ = _
    rw [eNU, L.mem_wr_ne (nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
      aS (by rw [vA, vst]; omega)]
    rw [w15.2.2 _ aS ?_]
    · exact hst
    rintro (hR | hR)
    · have := (hΩ _ (scW _ aS hR.inSC)).2.1 t htT; rw [vst] at this; omega
    · have vR : (L.nodeA (fS14 (L := L) S8 t dest r) layout.node.REPROGRAM).val = L.nodeBase s (L.cpu s) + 56 := by
        unfold LawfulStore.nodeA; rw [K.cpu, nodeAt_of_ksb K.ksb, nodeAt_val hN (by simp [layout.node.REPROGRAM])]
        simp [layout.node.REPROGRAM]
      have := congrArg UScalar.val hR; rw [vst, vR] at this; omega
  -- the handler's words
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) := KX.tw hdT 3464#u64 (by decide)
  have eInq : L.mem X (inqA dest) = L.mem s (inqA dest) := KX.tw hdT 3592#u64 (by decide)
  have ePr : L.mem X (prioA dest) = L.mem s (prioA dest) := KX.tw hdT 3448#u64 (by decide)
  have eAff : L.mem X (affA dest) = L.mem s (affA dest) := KX.tw hdT 3520#u64 (by decide)
  have eDom : L.mem X (domA dest) = L.mem s (domA dest) := KX.tw hdT 3432#u64 (by decide)
  have hp : (L.mem s (prioA dest)).val < 256 := hSQ.prio dest hdT
  have hRQs := hSQ.ready _ hcC
  have hRQX := ReadyQueues.keep hT hN hRQs KX
  have hdq : ∀ p' : U64, p'.val < 256 → dest ∉ Q (L.cpu s) p' := by
    intro p' hp' hm
    obtain ⟨ha, hpr⟩ := hSQ.inQ _ hcC p' hp' dest hm
    exact (hSQ.queued dest hdT).2 (by rw [ha, hpr]; exact hm) HF.nq
  have hle := le_of_is_hp hN hRQs.2 hhi
  have hhiX : sched.is_highest_prio st X 0#u64 (L.mem s (prioA dest)) = ok true :=
    is_hp_of_le 0#u64 hNX hRQX.2 hle
  -- `set_vm_root`'s reads
  have vm : ∀ w, Aligned w → NodeOrTcb (L := L) T s w → VmOff (L := L) s15 dest w :=
    fun w hw ho => vmOff_of hT hdT hN hcC hΩ hS.ksΩ hrS scSg hA K15 hw ho
  have vmQ : ∀ w, QW (L := L) T s w → VmOff (L := L) s15 dest w :=
    fun w hw => vm w (hw.aligned hT hN) (hw.nodeOrTcb hT hN)
  have haA : Aligned (actA (L := L) s15) := by
    show Aligned (L.nodeAt s15 (L.cpu s15) _); rw [eNU]
    exact nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have vmA : VmOff (L := L) s15 dest (actA (L := L) s15) :=
    vm _ haA (Or.inl ⟨layout.node.SCHED_ACTION, by simp [layout.node.SCHED_ACTION], eNU _⟩)
  -- the schedule reads are none of the enqueue's words
  have rdQ : ∀ lA : List U64, (∀ w ∈ lA, QW (L := L) T s w) →
      ∀ q ∈ schedRd (L := L) X, Aligned q ∧ ∀ w ∈ lA, Aligned w ∧ w ≠ q := by
    intro lA hlA q hq
    simp only [schedRd, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · refine ⟨?_, fun w hw => ⟨(hlA w hw).aligned hT hN, ?_⟩⟩
      · show Aligned (L.nodeAt X (L.cpu X) _); rw [eNX]
        exact nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      · show w ≠ L.nodeAt X (L.cpu X) _; rw [eNX]
        exact (hlA w hw).ne_node hT hN (by simp [layout.node.SCHED_ACTION])
    · refine ⟨?_, fun w hw => ⟨(hlA w hw).aligned hT hN, ?_⟩⟩
      · show Aligned (L.nodeAt X (L.cpu X) _); rw [eNX]
        exact nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      · show w ≠ L.nodeAt X (L.cpu X) _; rw [eNX]
        exact (hlA w hw).ne_node hT hN (by simp [layout.node.CUR_THREAD])
    · rw [hcur]
      refine ⟨aS, fun w hw => ⟨(hlA w hw).aligned hT hN, ?_⟩⟩
      rw [stA_eq]
      exact (hlA w hw).ne_tcb hT hN htT (by decide) (by decide) (by decide) (by decide)
    · rw [KX.ksb]
      have hm := hS.ksΩ layout.ks.DOMAIN_TIME (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
      exact ⟨(hΩ _ hm).1, fun w hw => ⟨(hlA w hw).aligned hT hN, (hlA w hw).ne_omg hT hN hcC (hΩ _ hm)⟩⟩
  have hvmL : ∀ lA : List U64, (∀ w ∈ lA, QW (L := L) T s w) → ∀ w ∈ actA (L := L) s15 :: lA,
      VmOff (L := L) s15 dest w := by
    intro lA hlA w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact vmA
    · exact vmQ w (hlA w hw)
  have hTM := hX0.tm.min _ hcC
  have hRel := fun h0 => rel_head (r := r) hSQ hB hS hX0 hO hr hdT HF.sc HF.nr h0
  -- the queue of the handler's priority
  have hQR := hRQs.1.rel _ hp
  have eqH : L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest)))) =
      L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA dest)))) := by
    rw [eNX]; exact KX.node _ (by rw [rqOff_val hp] <;> omega) (by rw [rqOff_val hp] <;> omega)
      (by rw [rqOff_val hp] <;> omega) (by rw [rqOff_val hp] <;> omega)
  have eqT : L.mem X (L.nodeAt X (L.cpu X) (rqTailOff (L.mem s (prioA dest)))) =
      L.mem s (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA dest)))) := by
    rw [eNX]; exact KX.node _ (by rw [rqTailOff_val hp] <;> omega) (by rw [rqTailOff_val hp] <;> omega)
      (by rw [rqTailOff_val hp] <;> omega) (by rw [rqTailOff_val hp] <;> omega)
  have qRq : QW (L := L) T s (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest)))) :=
    qw_nodeAt KX.ksb KX.cpu (by rw [rqOff_val hp] <;> omega) (by rw [rqOff_val hp] <;> omega)
      (by rw [rqOff_val hp] <;> omega)
  have qRt : QW (L := L) T s (L.nodeAt X (L.cpu X) (rqTailOff (L.mem s (prioA dest)))) :=
    qw_nodeAt KX.ksb KX.cpu (by rw [rqTailOff_val hp] <;> omega) (by rw [rqTailOff_val hp] <;> omega)
      (by rw [rqTailOff_val hp] <;> omega)
  have hhd0 : L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA dest)))) =
      (Q (L.cpu s) (L.mem s (prioA dest))).headD 0#u64 := hQR.head
  have htl0 : L.mem s (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA dest)))) =
      (Q (L.cpu s) (L.mem s (prioA dest))).getLastD 0#u64 := hQR.last
  have hcA : Aligned (curA (L := L) s15) := by
    show Aligned (L.nodeAt s15 (L.cpu s15) _); rw [eNU]
    exact nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have h1 : actA (L := L) s15 ≠ nextA .Sched dest := by
    show L.nodeAt s15 (L.cpu s15) _ ≠ _; rw [eNU]
    exact ((qw_next hdT).ne_node hT hN (by simp [layout.node.SCHED_ACTION])).symm
  have h2 : actA (L := L) s15 ≠ prevA .Sched dest := by
    show L.nodeAt s15 (L.cpu s15) _ ≠ _; rw [eNU]
    exact ((qw_prev hdT).ne_node hT hN (by simp [layout.node.SCHED_ACTION])).symm
  have h3 : actA (L := L) s15 ≠ curA (L := L) s15 := by
    show L.nodeAt s15 (L.cpu s15) _ ≠ L.nodeAt s15 (L.cpu s15) _; rw [eNU, eNU]
    intro e; have := congrArg UScalar.val e
    rw [nodeAt_val hN (by simp [layout.node.SCHED_ACTION]), nodeAt_val hN (by simp [layout.node.CUR_THREAD])] at this
    simp [layout.node.SCHED_ACTION, layout.node.CUR_THREAD] at this
  have hdomX : L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) = L.mem X (domA dest) := by
    rw [ksK _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]), eDom]; exact HF.dom
  have hdtX : L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME) ≠ 0#u64 := by
    rw [ksK _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])]; exact HF.dt
  have hnsX : ¬ (L.mem X (stA (L.mem X (curA (L := L) X))) = sched.TS_RUNNING ∨
      L.mem X (stA (L.mem X (curA (L := L) X))) = sched.TS_RESTART ∨
      L.mem X (stA (L.mem X (curA (L := L) X))) = sched.TS_RUNNING_VM) := by
    rw [hcur, hstX]
    simp [sched.TS_BLOCKED_ON_REPLY, sched.TS_RUNNING, sched.TS_RESTART, sched.TS_RUNNING_VM]
  have hscX : L.mem X (scA dest) ≠ 0#u64 := by rw [eSc]; exact HF.sc
  have hrqX : (L.mem X (inqA dest) &&& sched.Q_RELEASE) = 0#u64 := by rw [eInq]; exact HF.nr
  have hFC : FinCommon (L := L) T s15 dest (L.mem s (prioA dest)) (Q (L.cpu s)) := by
    subst hXd
    exact ⟨hscX, hrqX, hdomX, hRQX, hdq, hhiX, hnsX, hdtX, vmQ _ (qw_next hdT), vmQ _ (qw_prev hdT), haA, hcA,
      h1, h2, h3⟩
  refine ⟨T, L.mem s (prioA dest), Q (L.cpu s), hFC, ?_⟩
  rcases hl : Q (L.cpu s) (L.mem s (prioA dest)) with _ | ⟨h, rest'⟩
  · -- the empty queue
    rw [hl] at hhd0 htl0
    have hb := hRQX.2
    have hg : (L.mem s (prioA dest)).val / 64 < 4 := by omega
    have q1 : QW (L := L) T s (L.nodeAt X (L.cpu X) l1Off) :=
      qw_nodeAt KX.ksb KX.cpu (by rw [l1Off_val] <;> omega) (by rw [l1Off_val] <;> omega) (by rw [l1Off_val] <;> omega)
    have q2 : QW (L := L) T s (L.nodeAt X (L.cpu X) (l2Off ((L.mem s (prioA dest)).val / 64))) :=
      qw_nodeAt KX.ksb KX.cpu (by rw [l2Off_val hg] <;> omega) (by rw [l2Off_val hg] <;> omega)
        (by rw [l2Off_val hg] <;> omega)
    have hlA : ∀ w ∈ [L.nodeAt X (L.cpu X) l1Off, L.nodeAt X (L.cpu X) (l2Off ((L.mem s (prioA dest)).val / 64)),
        nextA .Sched dest, prevA .Sched dest, L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest))),
        L.nodeAt X (L.cpu X) (rqTailOff (L.mem s (prioA dest))), inqA dest], QW (L := L) T s w := by
      intro w hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact q1
      · exact q2
      · exact qw_next hdT
      · exact qw_prev hdT
      · exact qRq
      · exact qRt
      · exact qw_inq hdT
    refine Or.inr ⟨⟨hT, hdT, hNX, hp, by rw [eInq]; exact HF.nq, ePr, by rw [eAff, KX.cpu]; exact HF.aff,
      by rw [eqH, hhd0]; rfl, by rw [eqT, htl0]; rfl, ?_, ?_⟩, fun v1 v2 => ?_, rdQ _ hlA, hvmL _ hlA⟩
    · cases hbit : (L.l2W X (L.cpu X) ((L.mem s (prioA dest)).val / 64)).bv.getLsbD ((L.mem s (prioA dest)).val % 64)
      · rfl
      · have := (hb.l2 _ hp).1 hbit; rw [hl] at this; exact absurd rfl this
    · rw [hb.l1 _ (by omega)]
      exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
    · exact noDue_wrs hT hN hcC hΩ KX HF.nd hTM hRel
        [(L.nodeAt X (L.cpu X) l1Off, v1), (L.nodeAt X (L.cpu X) (l2Off ((L.mem s (prioA dest)).val / 64)), v2),
          (nextA .Sched dest, 0#u64), (prevA .Sched dest, 0#u64),
          (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest))), dest),
          (L.nodeAt X (L.cpu X) (rqTailOff (L.mem s (prioA dest))), dest),
          (inqA dest, L.mem X (inqA dest) ||| sched.Q_QUEUED)] fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact q1
        · exact q2
        · exact qw_next hdT
        · exact qw_prev hdT
        · exact qRq
        · exact qRt
        · exact qw_inq hdT
  · -- a nonempty queue
    rw [hl] at hhd0 htl0
    have hmem : ∀ y ∈ h :: rest', y ∈ T := fun y hy => hQR.mem y (by rw [hl]; exact hy)
    have hhT : h ∈ T := hmem h (by simp)
    have hH : L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest)))) = h := by rw [eqH, hhd0]; rfl
    have qP : QW (L := L) T s (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest)))))) := by
      rw [hH]; exact qw_prev hhT
    have hlA : ∀ w ∈ [nextA .Sched dest, prevA .Sched dest,
        prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest))))),
        L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest))),
        L.nodeAt X (L.cpu X) (rqTailOff (L.mem s (prioA dest))), inqA dest], QW (L := L) T s w := by
      intro w hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact qw_next hdT
      · exact qw_prev hdT
      · exact qP
      · exact qRq
      · exact qRt
      · exact qw_inq hdT
    have hseg := hQR.seg
    rw [hl] at hseg
    have hprev0 : L.mem s (prevA .Sched h) = 0#u64 := ((Seg_cons _ _ _ _ _ _).1 hseg).1
    refine Or.inl ⟨⟨hT, hdT, hNX, hp, by rw [eInq]; exact HF.nq, ePr, by rw [eAff, KX.cpu]; exact HF.aff,
      by rw [hH]; exact (hT h hhT).ne0 ∘ fun e => by rw [e]; rfl, by rw [hH]; exact hhT,
      by rw [hH]; exact fun e => hdq _ hp (by rw [hl, ← e]; simp),
      by rw [hH, show L.mem X (prevA .Sched h) = L.mem s (prevA .Sched h) from KX.tw hhT 3488#u64 (by decide)];
         exact hprev0,
      by rw [eqT, htl0]; exact fun e => hdq _ hp (by rw [hl, ← e]; exact getLastD_mem_cons _ _ _)⟩,
      ?_, rdQ _ hlA, hvmL _ hlA⟩
    exact noDue_wrs hT hN hcC hΩ KX HF.nd hTM hRel
      [(nextA .Sched dest, L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest))))), (prevA .Sched dest, 0#u64),
        (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest))))), dest),
        (L.nodeAt X (L.cpu X) (rqOff (L.mem s (prioA dest))), dest),
        (L.nodeAt X (L.cpu X) (rqTailOff (L.mem s (prioA dest))),
          L.mem X (L.nodeAt X (L.cpu X) (rqTailOff (L.mem s (prioA dest))))),
        (inqA dest, L.mem X (inqA dest) ||| sched.Q_QUEUED)] fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact qw_next hdT
      · exact qw_prev hdT
      · exact qP
      · exact qRq
      · exact qRt
      · exact qw_inq hdT

end

/-! ## (d3) The fault half's reads from one state, (d4) `entry_of6` -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **The fault fast path's placement facts at the state where
`fastpath.fault` is entered**, for the current thread `t`: the ASID placement
`AsidOff` [J] and, for every accepted check (`FaultChecks`), m61's
`FaultEnt` (the endpoint placed with its queue headed by the handler, the
handler not `t`, the user words and the receive buffer, the reply word among
`Ω`) with the handler's reply object among `Rp` (l4v `valid_ep`,
`sym_refs`, `valid_reply`; KENTRY-PLAN m61 (d3) lists the P1 facts each part
comes from). -/
def FaultEntAt (T Cs Ω U Sg Rp : Set U64) (s : S) (t : obj.Tcb) : Prop :=
  AsidOff (L := L) Ω Sg s ∧ ∀ ptr badge dest r, FaultChecks st s t ptr badge dest r →
    r ∈ Rp ∧ ∃ rest, FaultEnt (L := L) T Cs Ω U s t ptr dest r rest

/-- **m60's `FaultOK` from one state**: the P1 invariants where the fast path
is entered (`BXI`, what `budget_ok` leaves) and `FaultEntAt` there give the
general fault path's reads at every state it reaches (m58 `FaultReads`, m59
`UsOff`, m60 `FinReads`). -/
theorem faultOK_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {a : A}
    {t : obj.Tcb} {n : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t) : FaultOK (L := L) ar s a t n := by
  obtain ⟨⟨Q, R, hSQ⟩, hB, ⟨hO, -, hXE⟩, -, hS⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt s := hXE.toScExtra0
  intro ptr badge dest r hc rb sent S6 S7 S8 mi hbuf hmrs hmi hS7 hS8
  obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r hc
  obtain ⟨FR, -, K⟩ := faultReads_of ar E hbuf hmrs hS7 hS8
  have HF := here_facts (L := L) hc.here
  obtain ⟨d, p, -, hp, hhp⟩ := hc.prio
  have hp' : p = L.mem s (prioA dest) := by
    rw [eq_of_spec_fd (obj.Tcb.prio.spec (L := L) s dest)] at hp; exact (ok_inj_ff hp).symm
  have hhi : sched.is_highest_prio st s 0#u64 (L.mem s (prioA dest)) = ok true := by
    rw [← hp', is_highest_prio_dom s 0#u64 d]; exact hhp
  have hT := E.hT
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hd' := hT dest hdT
  have ht' := hT t E.ht
  have hdsc : L.mem s (scA dest) ∈ Scs := (hX0.bound dest hdT HF.sc).1
  obtain ⟨hPl, hZ7⟩ := hO.sc _ hdsc
  have scW : ∀ b, Aligned b → InSC (L.mem s (scA dest)) (Z (L.mem s (scA dest))) b → b ∈ Ω :=
    fun b hb h => hS.sub _ ((hS.all _ hdsc).2.2 b hb h)
  have spWF : L.mem s (sporA (L.mem s (scA dest))) ≠ 0#u64 →
      RefillsWF st s (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    fun h => (hS.all _ hdsc).1 ((hS.act _ hdsc).1 (hS.spor _ hdsc h))
  have hU := usOff_of E K scW (hS.sub _ (hS.spSg _ hdsc)) spWF (hO.rpSc r hr _ hdsc) hZ7 hPl.fits
  have aS : Aligned (stA t) := by
    show _ % 8 = 0; rw [stA_eq, tcb_wadd_val ht' (by decide)]; have := ht'.align; simp; omega
  have hne : stA dest ≠ stA t := by
    rw [stA_eq, stA_eq]; exact tcbw_ne hd' ht' (by decide) (by decide) (Or.inl E.hdt)
  have hst : L.mem (fS14 (L := L) S8 t dest r) (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    unfold fS14
    rw [mem_wr_ne' FR.hsA aS hne]; exact FR.hR13s
  exact ⟨T, rest, Z (L.mem s (scA dest)), FR, hU, fun s15 h15 =>
    finReads_of E HF hhi hSQ hB hS hX0 hO hr hF.1 K hst h15⟩

/-- **The fault half of the entry's fast-path premise, at the states where
`fastpath.fault` is entered** (m63 (d4)): after the `FAULT_IP` write and a
passing `budget_ok` (the trap route), and after a declined `debug_syscall`
then a passing `budget_ok` (the out-of-range route), `FaultEntAt` of the
current thread. Replaces m60's `FastFaultOK` (the general path's reads at the
five states it reaches) by facts at one state. -/
def FastFaultPre (T Cs Ω U Sg Rp : Set U64) (s : S) (a : A) (n : I64) : Prop :=
  ∀ t nx s1, sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    (∀ s2 a2 t2, syscall.budget_ok st ar s1 a = ok (true, s2, a2) → sched.cur_thread st s2 = ok t2 →
      FaultEntAt (L := L) T Cs Ω U Sg Rp s2 t2) ∧
    (∀ t1 s3 a3, sched.cur_thread st s1 = ok t1 → syscall.debug_syscall st ar s1 a t1 n = ok (false, s3, a3) →
      ∀ s2 a2 t2, syscall.budget_ok st ar s3 a3 = ok (true, s2, a2) → sched.cur_thread st s2 = ok t2 →
        FaultEntAt (L := L) T Cs Ω U Sg Rp s2 t2)

/-- **`FastFaultOK` from `FastFaultPre`** at an entry state (`EntryInv`, a
`P3Ok` state): the invariants where `fastpath.fault` is entered come from
`budget_ok.bxc` (after `reg_entry` for the `FAULT_IP` write and, on the
out-of-range route, `EntryHyps0.debug`). -/
theorem FastFaultOK.of_pre {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {P3Ok : S → Prop} (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} {n : I64} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hFP : FastFaultPre (L := L) ar T Cs Ω U Sg Rp s a n) : FastFaultOK (L := L) ar s a n := by
  intro t nx s1 et enx es1
  obtain ⟨hF1, hF2⟩ := hFP t nx s1 et enx es1
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  have htT : t ∈ T := by rw [et']; exact h.1.choose_spec.choose_spec.curT
  have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := reg_entry (r := layout.reg.FAULT_IP) (v := core.num.U64.wrapping_sub nx 2#u64) h htT
      (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at this; exact this
  have hW := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (h.1.choose_spec.choose_spec.tcbs t htT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW
  obtain ⟨K, hK, e1⟩ := hW
  have hal : Aligned (core.num.U64.wrapping_add (L.curW s) K) := by
    rw [← et']; exact field_aligned (h.1.choose_spec.choose_spec.tcbs t htT)
      (by rw [hK]; simp [layout.reg.FAULT_IP]) (by rw [hK]; simp [layout.reg.FAULT_IP])
  have he1 : EntAt st P3Ok s1 := ⟨s, hP, Ent.prefix hK hal (by rw [e1, et']) (WritesIn.refl _ _)⟩
  refine ⟨fun s2 a2 t2 hb et2 => ?_, fun t1 s3 a3 et1 hd => ?_⟩
  · have hx := syscall.budget_ok.bxc hA E0 s1 a h1 he1.xg
    rw [hb, WP.spec_ok] at hx
    exact faultOK_of ar hx.1 (hF1 s2 a2 t2 hb et2)
  · intro s2 a2 t2 hb et2
    have et1' : t1 = L.curW s1 := by
      rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s1)] at et1; exact (ok_inj_ff et1).symm
    have hd' := hd
    rw [et1'] at hd'
    have hdi := E0.debug Ac s1 a n he1 h1
    rw [hd', WP.spec_ok] at hdi
    obtain ⟨Ac3, h3⟩ := hdi
    have hsame := syscall.debug_syscall.same (L := L) hA s1 a (L.curW s1) n
    rw [hd', WP.spec_ok] at hsame
    have e3 : s3 = s1 := hsame rfl
    have hG3 : XG st T Cs Ω H Sg Scs Z P3Ok s3 := by rw [e3]; exact he1.xg
    have hx := syscall.budget_ok.bxc hA E0 s3 a3 h3 hG3
    rw [hb, WP.spec_ok] at hx
    exact faultOK_of ar hx.1 (hF2 t1 s3 a3 et1 hd s2 a2 t2 hb et2)

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **Native kernel entries keep `EntryInv`**, `entry_of5` with the fault
half's reads `FastFaultOK` (m60, a bundle over five intermediate states)
replaced by `FastFaultPre` (m63 (d4)): placement facts at the state where
`fastpath.fault` is entered — the ASID placement `AsidOff` [J] and m61's
`FaultEnt` for the accepted checks (to be derived from that state's P1
invariants and Hyps4's cap typing, KENTRY-PLAN m63 (d3) handoff). The P1
invariants there come from `budget_ok.bxc`. `StoreExt` [P] and the
ReplyRecv half `FastRRP` [P] unchanged. -/
theorem kernel_entry.entry_of6 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps4 st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hFP : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastFaultPre (L := L) ar T Cs Ω U Sg Rp s a number)
    (hRR : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastRRP (st := st) ar s a number (fun r => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' r.1)) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact (G.gaps3 hA hσ C Pd Pt P.xfer).gaps hA P C
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact kernel_entry.entry_of5 hA GF hσ s a hP h hX
    (fun number hN => FastFaultOK.of_pre ar hA E0 hP h (hFP number hN)) hRR

end

end Fl4Proofs.P1
