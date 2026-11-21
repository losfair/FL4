/-
# The accepted fault fast path: the scheduler half (FL4 #56, m59)

KENTRY-PLAN m58 handoff (a): after the meeting state of `fault_sync` the
general path runs `unblock_sporadic` on the state with the action word set
to `CHOOSE_NEW`, the fast path on the state without it. `refill_unblock_check`
reads and writes only words of the SC (header and the refills its ring
indices name, bounded by `RefillsWF`), the current core's `CUR_TIME` and
`REPROGRAM`; so it commutes with a write to any other aligned word
(`unblock_check_wr`, by induction over `unblock_check_loop`), and so does
`unblock_sporadic` (`unblock_sporadic_wr`). With that the two paths meet one
step later: `fault_sync2` (the general `handle_fault` is the fast path's
`unblock_sporadic` result, then the action word, then `possible_switch_to`).
-/
import Fl4Proofs.P1.FastFault
import Fl4Proofs.P1.QueueSc
import Fl4Proofs.P1.QueueRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## Exact forms of the ring operations -/

theorem pop_head_eq (s : S) (sc : obj.Sc) :
    sporadic.pop_head st s sc =
      ok (L.refill s sc (L.rhead s sc), L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) := by
  unfold sporadic.pop_head
  rw [eq_of_spec_fd (sporadic.head.spec (L := L) s sc), eq_of_spec_fd (obj.Sc.refill_head.spec (L := L) s sc)]
  simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (sporadic.next_index.spec (L := L) s sc _)]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Sc.set_refill_head.spec (L := L) s sc _)]; simp only [bind_ok, bind_tc_ok]

/-- One merge step of `refill_unblock_check`'s loop, as a state. -/
def ucStepS (s : S) (sc : obj.Sc) : S :=
  let s1 := L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))
  let old := L.refill s sc (L.rhead s sc)
  L.putS s1 sc (L.rhead s1 sc)
    { old with amount := core.num.U64.wrapping_add (L.refill s1 sc (L.rhead s1 sc)).amount old.amount }

theorem ucBody_eq (s : S) (sc : obj.Sc) (fuel : U64) :
    sporadic.unblock_check_loop.body st sc s fuel =
      if L.headOverlapping s sc = true then
        (if fuel > 0#u64 then (do let f1 ← fuel - 1#u64; ok (ControlFlow.cont (ucStepS (L := L) s sc, f1)))
          else ok (ControlFlow.done s))
      else ok (ControlFlow.done s) := by
  unfold sporadic.unblock_check_loop.body
  rw [eq_of_spec_fd (sporadic.head_overlapping.spec (L := L) s sc)]; simp only [bind_ok, bind_tc_ok]
  by_cases h1 : L.headOverlapping s sc = true
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : fuel > 0#u64
    · rw [if_pos h2, if_pos h2]
      obtain ⟨f1, hf1, -⟩ := spec_ex_fd (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
      rw [hf1]; simp only [bind_ok, bind_tc_ok]
      apply eq_of_spec_fd
      refine WP.spec_bind (spec_of_eq_fd (pop_head_eq s sc)) ?_
      rintro ⟨old, s1⟩ hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      refine WP.spec_bind (sporadic.head.spec (L := L) _ sc) ?_
      rintro h rfl
      simp only [lift, bind_ok, bind_tc_ok]
      refine WP.spec_bind (sporadic.set_head.eq (L := L) _ sc _) ?_
      rintro s2 rfl
      exact (WP.spec_ok _).2 rfl
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h1, if_neg h1]

/-- `unblock_check_loop` unfolded once. -/
theorem ucLoop_unfold (s : S) (sc : obj.Sc) (fuel : U64) :
    sporadic.unblock_check_loop st s sc fuel =
      (do
        let r ← sporadic.unblock_check_loop.body st sc s fuel
        match r with
        | ControlFlow.cont x => sporadic.unblock_check_loop st x.1 sc x.2
        | ControlFlow.done z => ok z) := by
  conv_lhs => unfold sporadic.unblock_check_loop; rw [loop]
  congr 1
  funext r
  cases r with
  | cont x => obtain ⟨a, b⟩ := x; rfl
  | done z => rfl

/-! ## Reads of the SC past a write outside it -/

variable {sb : Nat}

theorem mem_wr_outside {s : S} {sc : obj.Sc} {A v x : U64} (hA : Aligned A) (hAo : Outside A sc sb)
    (hx : Aligned x) (h1 : sc.val ≤ x.val) (h2 : x.val < sc.val + 2 ^ sb) : L.mem (L.wr s A v) x = L.mem s x :=
  L.mem_wr_ne hA hx (by unfold Outside at hAo; omega)

theorem ne_of_outside {sc : obj.Sc} {A x : U64} (hAo : Outside A sc sb) (h1 : sc.val ≤ x.val)
    (h2 : x.val < sc.val + 2 ^ sb) : A ≠ x := by
  intro e; subst e; unfold Outside at hAo; omega

structure SCView (s s' : S) (sc : obj.Sc) : Prop where
  max : L.rmax s' sc = L.rmax s sc
  head : L.rhead s' sc = L.rhead s sc
  tail : L.rtail s' sc = L.rtail s sc
  period : L.rperiod s' sc = L.rperiod s sc
  refill : ∀ i : U64, i.val < (L.rmax s sc).val → L.refill s' sc i = L.refill s sc i

theorem SCView.of_wr {s : S} {sc : obj.Sc} {A v : U64} (hW : RefillsWF st s sc sb) (hA : Aligned A)
    (hAo : Outside A sc sb) : SCView (L := L) s (L.wr s A v) sc := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have := hW.min_le; simp at this
  have e : ∀ x, Aligned x → sc.val ≤ x.val → x.val < sc.val + 2 ^ sb → L.mem (L.wr s A v) x = L.mem s x :=
    fun x hx h1 h2 => mem_wr_outside hA hAo hx h1 h2
  refine ⟨e _ (by addr) (by addr) (by addr), e _ (by addr) (by addr) (by addr),
    e _ (by addr) (by addr) (by addr), e _ (by addr) (by addr) (by addr), fun i hi => ?_⟩
  unfold LawfulStore.refill
  rw [e _ (by addr) (by addr) (by addr), e _ (by addr) (by addr) (by addr)]

theorem SCView.headOverlapping {s s' : S} {sc : obj.Sc} (hW : RefillsWF st s sc sb) (h : SCView (L := L) s s' sc) :
    L.headOverlapping s' sc = L.headOverlapping s sc := by
  unfold LawfulStore.headOverlapping
  rw [h.head, h.tail, h.max, h.refill _ hW.head_lt, h.refill _ (nextIdx_lt hW.head_lt)]

/-- `putS` past a write outside the SC. -/
theorem putS_wr {s : S} {sc : obj.Sc} {A v i : U64} {r : sporadic.Refill} (hX : StoreExt st)
    (hW : RefillsWF st s sc sb) (hA : Aligned A) (hAo : Outside A sc sb) (hi : i.val < (L.rmax s sc).val) :
    L.putS (L.wr s A v) sc i r = L.wr (L.putS s sc i r) A v := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  unfold LawfulStore.putS
  have a1 : Aligned (rtA sc i) := by addr
  have a2 : Aligned (raA sc i) := by addr
  rw [wr_comm hX _ _ _ hA a1 (ne_of_outside hAo (by addr) (by addr)),
    wr_comm hX _ _ _ hA a2 (ne_of_outside hAo (by addr) (by addr))]

theorem wr_head_wr {s : S} {sc : obj.Sc} {A v w : U64} (hX : StoreExt st) (hW : RefillsWF st s sc sb)
    (hA : Aligned A) (hAo : Outside A sc sb) :
    L.wr (L.wr s A v) (headA sc) w = L.wr (L.wr s (headA sc) w) A v := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have := hW.min_le; simp at this
  exact wr_comm hX _ _ _ hA (by addr) (ne_of_outside hAo (by addr) (by addr))

theorem RefillsWF.ucStep {s : S} {sc : obj.Sc} (hW : RefillsWF st s sc sb) :
    RefillsWF st (ucStepS (L := L) s sc) sc sb := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have h1 := hW.wr_head (v := nextIdx (L.rmax s sc) (L.rhead s sc)) (nextIdx_lt hW.head_lt)
  unfold ucStepS
  refine h1.putS ?_
  rw [rhead_wr_head h8, rmax_wr_head h8]; exact nextIdx_lt hW.head_lt

theorem ucStepS_wr {s : S} {sc : obj.Sc} {A v : U64} (hX : StoreExt st) (hW : RefillsWF st s sc sb)
    (hA : Aligned A) (hAo : Outside A sc sb) :
    ucStepS (L := L) (L.wr s A v) sc = L.wr (ucStepS (L := L) s sc) A v := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have V := SCView.of_wr (v := v) hW hA hAo
  have h1 := hW.wr_head (v := nextIdx (L.rmax s sc) (L.rhead s sc)) (nextIdx_lt hW.head_lt)
  have V1 := SCView.of_wr (v := v) h1 hA hAo
  have hn : (L.rhead (L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) sc).val <
      (L.rmax (L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) sc).val := h1.head_lt
  unfold ucStepS
  simp only [V.max, V.head, V.refill _ hW.head_lt]
  rw [wr_head_wr hX hW hA hAo]
  simp only [V1.head, V1.refill _ hn]
  exact putS_wr hX h1 hA hAo hn

/-- **`unblock_check_loop` commutes with a write outside the SC.** -/
theorem ucLoop_wr {sc : obj.Sc} {A v : U64} (hX : StoreExt st) (hA : Aligned A) (hAo : Outside A sc sb) :
    ∀ (n : Nat) (s : S) (fuel : U64), fuel.val = n → RefillsWF st s sc sb →
      sporadic.unblock_check_loop st (L.wr s A v) sc fuel =
        (sporadic.unblock_check_loop st s sc fuel) >>= fun s' => ok (L.wr s' A v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s fuel hn hW
  rw [ucLoop_unfold, ucLoop_unfold (s := s), ucBody_eq, ucBody_eq,
    (SCView.of_wr (v := v) hW hA hAo).headOverlapping hW]
  by_cases h1 : L.headOverlapping s sc = true
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : fuel > 0#u64
    · rw [if_pos h2, if_pos h2]
      obtain ⟨f1, hf1, hv⟩ := spec_ex_fd (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
      rw [hf1]; simp only [bind_ok, bind_tc_ok]
      rw [ucStepS_wr hX hW hA hAo]
      exact ih f1.val (by scalar_tac) _ f1 rfl hW.ucStep
    · rw [if_neg h2, if_neg h2]; simp only [bind_ok, bind_tc_ok]
  · rw [if_neg h1, if_neg h1]; simp only [bind_ok, bind_tc_ok]

theorem ne_val {a b : U64} (h : a ≠ b) : a.val ≠ b.val := fun e => h (UScalar.eq_of_val_eq e)

/-- **`refill_unblock_check` commutes with a write to an aligned word outside
the SC other than the current core's `CUR_TIME` and `REPROGRAM`** (m58
handoff (a); `REPROGRAM` outside the SC as in `unblock_check.fr`). -/
theorem unblock_check_wr {s : S} {sc : obj.Sc} {A v : U64} (hX : StoreExt st) (hW : RefillsWF st s sc sb)
    (hA : Aligned A) (hAo : Outside A sc sb)
    (hct : Aligned (L.nodeA s layout.node.CUR_TIME)) (hAct : A ≠ L.nodeA s layout.node.CUR_TIME)
    (hrp : Aligned (L.nodeA s layout.node.REPROGRAM) ∧ Outside (L.nodeA s layout.node.REPROGRAM) sc sb)
    (hArp : A ≠ L.nodeA s layout.node.REPROGRAM) :
    sporadic.unblock_check st (L.wr s A v) sc =
      (sporadic.unblock_check st s sc) >>= fun s' => ok (L.wr s' A v) := by
  have V := SCView.of_wr (v := v) hW hA hAo
  have hcT : L.curTime (L.wr s A v) = L.curTime s := by
    unfold LawfulStore.curTime; rw [nodeA_wr, L.mem_wr_ne hA hct (ne_val hAct)]
  unfold sporadic.unblock_check
  rw [eq_of_spec_fd (sporadic.is_round_robin.spec (L := L) (L.wr s A v) sc),
    eq_of_spec_fd (sporadic.is_round_robin.spec (L := L) s sc), V.period]
  simp only [bind_ok, bind_tc_ok]
  by_cases h0 : L.rperiod s sc = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]; simp only [bind_ok, bind_tc_ok]
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [eq_of_spec_fd (sporadic.ready.spec (L := L) (L.wr s A v) sc),
    eq_of_spec_fd (sporadic.ready.spec (L := L) s sc), V.head, V.refill _ hW.head_lt, hcT]
  simp only [bind_ok, bind_tc_ok]
  by_cases h1 : (L.refill s sc (L.rhead s sc)).time ≤ L.curTime s
  swap
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]; simp only [bind_ok, bind_tc_ok]
  simp only [h1, decide_true, ↓reduceIte]
  rw [eq_of_spec_fd (sporadic.cur_time.spec (L := L) (L.wr s A v)),
    eq_of_spec_fd (sporadic.cur_time.spec (L := L) s), hcT]
  simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (sporadic.head.spec (L := L) (L.wr s A v) sc),
    eq_of_spec_fd (sporadic.head.spec (L := L) s sc), V.head, V.refill _ hW.head_lt]
  simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (sporadic.set_head.eq (L := L) (L.wr s A v) sc _),
    eq_of_spec_fd (sporadic.set_head.eq (L := L) s sc _), V.head, putS_wr hX hW hA hAo hW.head_lt]
  simp only [bind_ok, bind_tc_ok]
  rw [L.cur_cpu_eq, L.cur_cpu_eq]; simp only [bind_ok, L.cpu_wr]
  set P := L.putS s sc (L.rhead s sc) { L.refill s sc (L.rhead s sc) with time := L.curTime s } with hP
  have hWP : RefillsWF st P sc sb := hW.putS hW.head_lt
  have hcpu : L.cpu P = L.cpu s := by rw [hP]; simp [LawfulStore.putS]
  have hR : L.nodeAt P (L.cpu P) layout.node.REPROGRAM = L.nodeA s layout.node.REPROGRAM := by
    rw [hP]; simp [LawfulStore.putS, LawfulStore.nodeA]
  rw [eq_of_spec_fd (obj.node_set.spec (L := L) (L.wr P A v) _ _ _),
    eq_of_spec_fd (obj.node_set.spec (L := L) P _ _ _)]
  simp only [bind_ok, nodeAt_wr, hR]
  rw [wr_comm hX _ _ _ hA hrp.1 hArp]
  have hWQ : RefillsWF st (L.wr P (L.nodeA s layout.node.REPROGRAM) 1#u64) sc sb := hWP.wr_out hrp.1 hrp.2
  rw [eq_of_spec_fd (obj.Sc.refill_max.spec (L := L) (L.wr (L.wr P _ 1#u64) A v) sc),
    eq_of_spec_fd (obj.Sc.refill_max.spec (L := L) (L.wr P _ 1#u64) sc),
    (SCView.of_wr (v := v) hWQ hA hAo).max]
  simp only [bind_ok, lift]
  exact ucLoop_wr hX hA hAo _ _ _ rfl hWQ

theorem sc_sporadic_eq (s : S) (sc : obj.Sc) :
    sporadic.sc_sporadic st s sc = ok (if sc = 0#u64 then false else (L.mem s (sporA sc) != 0#u64)) := by
  unfold sporadic.sc_sporadic
  rw [eq_of_spec_fd (obj.Sc.is_null.spec sc)]; simp only [bind_ok, bind_tc_ok]
  by_cases h : sc = 0#u64
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    unfold obj.Sc.sporadic; simp [lift, L.read_eq, sporA]

/-- The words `unblock_sporadic dest` reads outside the SC, and what
`unblock_check_wr` needs of its SC, for a write to `A`. -/
structure UsOff (s : S) (d : obj.Tcb) (A : U64) (sb : Nat) : Prop where
  hA : Aligned A
  scAl : Aligned (scA d)
  AscA : A ≠ scA d
  csc : Aligned (L.nodeA s layout.node.CUR_SC)
  Acsc : A ≠ L.nodeA s layout.node.CUR_SC
  /-- The SC's `SPORADIC` word (read before `unblock_check` is decided). -/
  sp : Aligned (sporA (L.mem s (scA d))) ∧ A ≠ sporA (L.mem s (scA d))
  /-- Refills well formed where `unblock_check` runs: a sporadic SC (active,
  l4v `valid_refills` under `sc_active`; m61: m60 asked it of every nonzero SC,
  false for a bound SC that was never configured). -/
  wf : L.mem s (scA d) ≠ 0#u64 → L.mem s (sporA (L.mem s (scA d))) ≠ 0#u64 → RefillsWF st s (L.mem s (scA d)) sb
  out : Outside A (L.mem s (scA d)) sb
  ct : Aligned (L.nodeA s layout.node.CUR_TIME)
  Act : A ≠ L.nodeA s layout.node.CUR_TIME
  rp : Aligned (L.nodeA s layout.node.REPROGRAM) ∧ Outside (L.nodeA s layout.node.REPROGRAM) (L.mem s (scA d)) sb
  Arp : A ≠ L.nodeA s layout.node.REPROGRAM

/-- **`unblock_sporadic` commutes with a write outside what it reads.** -/
theorem unblock_sporadic_wr {s : S} {d : obj.Tcb} {A v : U64} (hX : StoreExt st) (h : UsOff (L := L) s d A sb) :
    endpoint.unblock_sporadic st (L.wr s A v) d =
      (endpoint.unblock_sporadic st s d) >>= fun s' => ok (L.wr s' A v) := by
  unfold endpoint.unblock_sporadic
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) (L.wr s A v) d), eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s d),
    L.mem_wr_ne h.hA h.scAl (ne_val h.AscA)]
  simp only [bind_ok, bind_tc_ok]
  rw [sc_sporadic_eq, sc_sporadic_eq]; simp only [bind_ok, bind_tc_ok]
  by_cases h0 : L.mem s (scA d) = 0#u64
  · simp only [h0, ↓reduceIte, Bool.false_eq_true]; simp only [bind_ok, bind_tc_ok]
  have hsp : L.mem (L.wr s A v) (sporA (L.mem s (scA d))) = L.mem s (sporA (L.mem s (scA d))) :=
    L.mem_wr_ne h.hA h.sp.1 (ne_val h.sp.2)
  simp only [h0, ↓reduceIte, hsp]
  by_cases h1 : (L.mem s (sporA (L.mem s (scA d))) != 0#u64) = true
  swap
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]; simp only [bind_ok, bind_tc_ok]
  have hW := h.wf h0 (bne_iff_ne.1 h1)
  simp only [h1, ↓reduceIte]
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) (L.wr s A v)), eq_of_spec_fd (sched.cur_sc.spec (L := L) s),
    nodeA_wr, L.mem_wr_ne h.hA h.csc (ne_val h.Acsc)]
  simp only [bind_ok, bind_tc_ok]
  obtain ⟨b1, hb1, -⟩ := spec_ex_fd (sc_ne.spec (L.mem s (scA d)) (L.mem s (L.nodeA s layout.node.CUR_SC)))
  rw [hb1]; simp only [bind_ok, bind_tc_ok]
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte]; simp only [bind_ok, bind_tc_ok]
  · simp only [↓reduceIte]
    exact unblock_check_wr hX hW h.hA h.out h.ct h.Act h.rp h.Arp

end

/-! ## The meeting state, one step later -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- The fast path's `unblock_sporadic` is the general one (the same reads and
`unblock_check`, inlined in fastpath.rs). -/
theorem faultTail3_eq (S14 : S) (a : A) (dest : U64) :
    faultTail3 st ar S14 a dest =
      (do
        let s15 ← endpoint.unblock_sporadic st S14 dest
        let s16 ← obj.Tcb.set_sched_next st dest s15 0#u64
        let s17 ← obj.Tcb.set_sched_prev st dest s16 0#u64
        let (s18, a1) ← fastpath.switch_to st ar s17 a dest
        ok (true, s18, a1)) := by
  unfold faultTail3 endpoint.unblock_sporadic
  simp only [Std.bind_assoc, bind_tc_ok, bind_ok]
  all_goals rfl

/-- **The two fault paths meet after `unblock_sporadic`** (m58 handoff (a)):
from `fault_sync`'s `S14` both run the same `unblock_sporadic S14 dest`; the
general path then has the action word `CHOOSE_NEW` written and runs
`possible_switch_to`, the fast path clears the handler's scheduler links and
runs `switch_to`. -/
theorem fault_sync2 (hX : StoreExt st) {T : Set U64} {sb : Nat} {s : S} {a : A} {t : obj.Tcb}
    {n ptr badge dest r : U64} {sF : S} {aF : A} (hc : FaultChecks st s t ptr badge dest r)
    (hfast : faultTail st ar s a t n ptr badge dest r = ok (true, sF, aF))
    (hR : ∀ (rb sent : U64) (S6 S7 S8 : S) (mi : msginfo.MessageInfo),
      msg.lookup_ipc_buffer st (epFast (L := L) (sfW (L := L) s t n) ptr dest) true dest = ok rb →
      faults.set_mrs_fault st ar (epFast (L := L) (sfW (L := L) s t n) ptr dest) a t dest rb = ok (sent, S6) →
      msginfo.MessageInfo.new fl4_abi.consts.fault.UnknownSyscall 0#u64 0#u64 sent = ok mi →
      msg.set_msg_info st S6 dest mi = ok S7 →
      obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8 →
      ∃ rest, FaultReads (L := L) T s t n ptr dest r rest S6 S8) :
    ∃ S14 : S,
      (do
        let s15 ← endpoint.unblock_sporadic st S14 dest
        let s16 ← obj.Tcb.set_sched_next st dest s15 0#u64
        let s17 ← obj.Tcb.set_sched_prev st dest s16 0#u64
        let (s18, a1) ← fastpath.switch_to st ar s17 a dest
        ok (true, s18, a1)) = ok (true, sF, aF) ∧
      (UsOff (L := L) S14 dest (actA (L := L) S14) sb →
        faults.handle_fault st ar s a t (error.Fault.UnknownSyscall n) =
          (do
            let s6 ← endpoint.unblock_sporadic st S14 dest
            let s7 ← sched.possible_switch_to st (L.wr s6 (actA (L := L) S14) sched.ACTION_CHOOSE_NEW) dest
            ok (s7, a))) := by
  obtain ⟨S14, h1, h2⟩ := fault_sync ar hX hc hfast hR
  refine ⟨S14, by rw [← faultTail3_eq]; exact h1, fun hU => ?_⟩
  rw [h2, unblock_sporadic_wr hX hU]
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok]

end

/-! ## `finish` after the fault: the no-op parts (m58 handoff (c)) -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- With one domain `check_domain_time` does nothing. -/
theorem check_domain_time_one (s : S) : sched.check_domain_time st s = ok s := by
  unfold sched.check_domain_time sched.is_cur_domain_expired
  rw [if_neg num_domains_one]; simp only [bind_ok, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]

/-- `timer.fire` with no timeout due (the earliest timer is empty or later
than `CUR_TIME`: what `schedulable_here` checked) does nothing. -/
theorem timer_fire_none (s : S) (a : A)
    (h : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) <
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) :
    timer.fire st ar s a = ok (s, a) := by
  unfold timer.fire timer.fire_loop
  rw [L.cur_cpu_eq]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s _ _)]; simp only [bind_ok, bind_tc_ok]
  rw [loop]
  unfold timer.fire_loop.body
  have hb : (0#u64 : U64) < timer.FIRE_BATCH := by unfold timer.FIRE_BATCH; decide
  simp only [hb, ↓reduceIte, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s _ _)]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec _)]; simp only [bind_ok, bind_tc_ok]
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte, bind_ok, bind_tc_ok]
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s _)]; simp only [bind_ok, bind_tc_ok]
  have h1 := h.resolve_left h0
  have h1' : L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) >
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) := h1
  simp only [h1', ↓reduceIte, bind_ok, bind_tc_ok]

/-- `awaken_loop` with no release due (the release queue is empty or its
head's SC is not ready) does nothing. -/
theorem awaken_loop_none (s : S) (fuel : U64)
    (h : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime s)) :
    sched.awaken_loop st s fuel = ok s := by
  unfold sched.awaken_loop
  rw [loop]
  unfold sched.awaken_loop.body
  by_cases hf : fuel > 0#u64
  swap
  · simp only [hf, ↓reduceIte, bind_ok, bind_tc_ok]
  obtain ⟨f1, hf1, -⟩ := spec_ex_fd (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
  simp only [hf, ↓reduceIte, hf1, L.cur_cpu_eq, bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s _ _)]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec _)]; simp only [bind_ok, bind_tc_ok]
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte, bind_ok, bind_tc_ok]
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s _)]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (sporadic.ready.spec (L := L) s _)]; simp only [bind_ok, bind_tc_ok]
  have h1 := h.resolve_left h0
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, bind_tc_ok]

/-- `awaken` with nothing due does nothing. -/
theorem awaken_none (s : S) (a : A)
    (hT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) <
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (hR : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime s)) :
    sched.awaken st ar s a = ok (s, a) := by
  unfold sched.awaken
  rw [timer_fire_none ar s a hT]; simp only [bind_ok, bind_tc_ok]
  exact (show (do let s2 ← sched.awaken_loop st s layout.WALK_FUEL; ok (s2, a)) = ok (s, a) by
    rw [awaken_loop_none s _ hR]; simp only [bind_ok, bind_tc_ok])

end

/-! ## `enqueue` then `dequeue` of the handler (m58 handoff (c), F3) -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem mem_wr_ne' {s : S} {a b v : U64} (ha : Aligned a) (hb : Aligned b) (h : a ≠ b) :
    L.mem (L.wr s a v) b = L.mem s b := L.mem_wr_ne ha hb (ne_val h)

theorem tcb_wadd_val {t o : U64} (h : TcbAddr t) (ho : o.val < 4096) :
    (core.num.U64.wrapping_add t o).val = t.val + o.val := by
  have := h.fits; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem or_andn_qq (x : U64) (h : (x &&& sched.Q_QUEUED) = 0#u64) :
    (x ||| sched.Q_QUEUED) &&& ~~~sched.Q_QUEUED = x := by
  have z : (0#u64).bv = 0#64 := rfl
  have h0 : x.bv.getLsbD 0 = false := by
    have e := congrArg (fun y : U64 => y.bv.getLsbD 0) h
    simp only [qq_val, UScalar.bv_and, BitVec.getLsbD_and, one_bit, z, BitVec.getLsbD_zero] at e
    simpa using e
  rw [qq_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit]
  by_cases hi0 : i = 0
  · subst hi0
    simp
    first | exact h0 | (rw [← BitVec.getLsbD_eq_getElem]; exact h0) | simpa using h0
  · simp [hi0, hi]

theorem prepend_ne (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : U64) (h : q.head ≠ 0#u64) :
    tcbqueue.prepend st s l q t =
      ok ({ q with head := t }, L.wr (L.wr (L.wr s (nextA l t) q.head) (prevA l t) 0#u64) (prevA l q.head) t) := by
  unfold tcbqueue.prepend
  rw [eq_of_spec_fd (tcbqueue.Queue.is_empty.spec q)]
  simp only [bind_ok, bind_tc_ok, h, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [eq_of_spec_fd (tcbqueue.set_next.spec (L := L) s l t _)]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (tcbqueue.set_prev.spec (L := L) _ l t _)]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (tcbqueue.set_prev.spec (L := L) _ l q.head _)]; simp only [bind_ok, bind_tc_ok]

/-- The state after `enqueue d` on a nonempty ready queue (head word `H`, tail
word `E`). -/
def enqNE (X : S) (d H E : U64) : S :=
  L.wr (L.wr (L.wr (L.wr (L.wr (L.wr X (nextA .Sched d) (L.mem X H)) (prevA .Sched d) 0#u64)
    (prevA .Sched (L.mem X H)) d) H d) E (L.mem X E)) (inqA d) (L.mem X (inqA d) ||| sched.Q_QUEUED)

/-- What `enqueue d` then `dequeue d` on a nonempty ready queue read (F3:
the old head has `sched_prev = 0`, the tail is not `d`; `d` not queued, on
this core, its priority `p`). -/
structure EnqNE (T : Set U64) (X : S) (d p : U64) : Prop where
  hT : TcbPlaced T
  hd : d ∈ T
  hN : NodePlaced st T X (L.cpu X)
  hp : p.val < 256
  hq : (L.mem X (inqA d) &&& sched.Q_QUEUED) = 0#u64
  hpr : L.mem X (prioA d) = p
  haff : L.mem X (affA d) = L.cpu X
  hh0 : L.mem X (L.nodeAt X (L.cpu X) (rqOff p)) ≠ 0#u64
  hhT : L.mem X (L.nodeAt X (L.cpu X) (rqOff p)) ∈ T
  hhd : L.mem X (L.nodeAt X (L.cpu X) (rqOff p)) ≠ d
  hhp : L.mem X (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) = 0#u64
  hed : L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ d


/-- The addresses `enqueue` / `dequeue` touch, as numbers (for `omega`). -/
theorem EnqNE.vals {T : Set U64} {X : S} {d p : U64} (E : EnqNE (L := L) T X d p) :
    (nextA .Sched d).val = d.val + 3480 ∧ (prevA .Sched d).val = d.val + 3488 ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))).val =
      (L.mem X (L.nodeAt X (L.cpu X) (rqOff p))).val + 3488 ∧
    (L.nodeAt X (L.cpu X) (rqOff p)).val = L.nodeBase X (L.cpu X) + (168 + 16 * p.val) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)).val = L.nodeBase X (L.cpu X) + (176 + 16 * p.val) ∧
    (inqA d).val = d.val + 3592 ∧ (affA d).val = d.val + 3520 ∧ (domA d).val = d.val + 3432 ∧
    (prioA d).val = d.val + 3448 ∧
    d.val % 4096 = 0 ∧ (L.mem X (L.nodeAt X (L.cpu X) (rqOff p))).val % 4096 = 0 ∧
    d.val + 4096 ≤ 2 ^ 64 ∧ (L.mem X (L.nodeAt X (L.cpu X) (rqOff p))).val + 4096 ≤ 2 ^ 64 ∧
    d.val ≠ (L.mem X (L.nodeAt X (L.cpu X) (rqOff p))).val ∧
    (d.val + 4096 ≤ L.nodeBase X (L.cpu X) ∨ L.nodeBase X (L.cpu X) + 4288 ≤ d.val) ∧
    ((L.mem X (L.nodeAt X (L.cpu X) (rqOff p))).val + 4096 ≤ L.nodeBase X (L.cpu X) ∨
      L.nodeBase X (L.cpu X) + 4288 ≤ (L.mem X (L.nodeAt X (L.cpu X) (rqOff p))).val) ∧
    L.nodeBase X (L.cpu X) % 8 = 0 ∧ p.val < 256 := by
  have hda := E.hT d E.hd
  have hha := E.hT _ E.hhT
  have hdh : d.val ≠ (L.mem X (L.nodeAt X (L.cpu X) (rqOff p))).val := fun e => E.hhd (UScalar.eq_of_val_eq e).symm
  have hp := E.hp
  have r1 := rqOff_val E.hp
  have r2 := rqTailOff_val E.hp
  have v1 := nodeAt_val E.hN (off := rqOff p) (by omega)
  have v2 := nodeAt_val E.hN (off := rqTailOff p) (by omega)
  have n1 := nextA_val hda .Sched
  have n2 := prevA_val hda .Sched
  have n3 := prevA_val hha .Sched
  have n7 : (affA d).val = d.val + 3520 := by unfold affA; rw [tcb_wadd_val hda (by decide)]; rfl
  have n8 : (domA d).val = d.val + 3432 := by unfold domA; rw [tcb_wadd_val hda (by decide)]; rfl
  have n9 : (prioA d).val = d.val + 3448 := by unfold prioA; rw [tcb_wadd_val hda (by decide)]; rfl
  simp only [nextOff, prevOff] at n1 n2 n3
  have o1 : (3480#u64 : U64).val = 3480 := rfl
  have o2 : (3488#u64 : U64).val = 3488 := rfl
  rw [o1] at n1; rw [o2] at n2 n3
  rw [r1] at v1; rw [r2] at v2
  exact ⟨n1, n2, n3, v1, v2, inqA_val hda, n7, n8, n9, hda.align, hha.align, hda.fits, hha.fits, hdh,
    E.hN.disj d E.hd, E.hN.disj _ E.hhT, E.hN.align, hp⟩


/-- The alignment and pairwise distinctness of the words `enqueue` /
`dequeue` touch (both orientations, for `simp`'s discharger). -/
theorem EnqNE.facts {T : Set U64} {X : S} {d p : U64} (E : EnqNE (L := L) T X d p) :
    Aligned (nextA .Sched d) ∧
    Aligned (prevA .Sched d) ∧
    Aligned (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    Aligned (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    Aligned (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    Aligned (inqA d) ∧
    Aligned (affA d) ∧
    Aligned (domA d) ∧
    Aligned (prioA d) ∧
    (nextA .Sched d) ≠ (prevA .Sched d) ∧
    (nextA .Sched d) ≠ (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    (nextA .Sched d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (nextA .Sched d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (nextA .Sched d) ≠ (inqA d) ∧
    (nextA .Sched d) ≠ (affA d) ∧
    (nextA .Sched d) ≠ (domA d) ∧
    (nextA .Sched d) ≠ (prioA d) ∧
    (prevA .Sched d) ≠ (nextA .Sched d) ∧
    (prevA .Sched d) ≠ (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    (prevA .Sched d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (prevA .Sched d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (prevA .Sched d) ≠ (inqA d) ∧
    (prevA .Sched d) ≠ (affA d) ∧
    (prevA .Sched d) ≠ (domA d) ∧
    (prevA .Sched d) ≠ (prioA d) ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ≠ (nextA .Sched d) ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ≠ (prevA .Sched d) ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ≠ (inqA d) ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ≠ (affA d) ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ≠ (domA d) ∧
    (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ≠ (prioA d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (nextA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (prevA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (inqA d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (affA d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (domA d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (prioA d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (nextA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (prevA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (inqA d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (affA d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (domA d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (prioA d) ∧
    (inqA d) ≠ (nextA .Sched d) ∧
    (inqA d) ≠ (prevA .Sched d) ∧
    (inqA d) ≠ (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    (inqA d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (inqA d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (inqA d) ≠ (affA d) ∧
    (inqA d) ≠ (domA d) ∧
    (inqA d) ≠ (prioA d) ∧
    (affA d) ≠ (nextA .Sched d) ∧
    (affA d) ≠ (prevA .Sched d) ∧
    (affA d) ≠ (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    (affA d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (affA d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (affA d) ≠ (inqA d) ∧
    (affA d) ≠ (domA d) ∧
    (affA d) ≠ (prioA d) ∧
    (domA d) ≠ (nextA .Sched d) ∧
    (domA d) ≠ (prevA .Sched d) ∧
    (domA d) ≠ (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    (domA d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (domA d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (domA d) ≠ (inqA d) ∧
    (domA d) ≠ (affA d) ∧
    (domA d) ≠ (prioA d) ∧
    (prioA d) ≠ (nextA .Sched d) ∧
    (prioA d) ≠ (prevA .Sched d) ∧
    (prioA d) ≠ (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) ∧
    (prioA d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (prioA d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (prioA d) ≠ (inqA d) ∧
    (prioA d) ≠ (affA d) ∧
    (prioA d) ≠ (domA d) := by
  obtain ⟨n1, n2, n3, v1, v2, n6, n7, n8, n9, al1, al2, f1, f2, hdh, dj1, dj2, ba, hp⟩ := E.vals
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold Aligned; omega)
    | (intro e; have := congrArg UScalar.val e; omega)

/-- Discharges alignment and distinctness side conditions from the numeric
address facts in context. -/
macro "mdisch" : tactic => `(tactic| first
  | assumption
  | (simp only [Aligned]; omega)
  | (intro e; have := congrArg UScalar.val e; omega)
  | omega)

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **`enqueue d` on a nonempty ready queue** (the handler, F3 facts in
`EnqNE`): `d` becomes the head. The memory reads are proved on explicit
terms first and rewritten in (`simp (disch := assumption)` over the named facts of `EnqNE.facts`: the default discharger does not close the `Aligned` side conditions). -/
theorem enqueue_ne {T : Set U64} {X : S} {d p : U64} (E : EnqNE (L := L) T X d p) :
    sched.enqueue st X d = ok (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) := by
  obtain ⟨n1, n2, n3, v1, v2, n6, n7, n8, n9, al1, al2, f1, f2, hdh, dj1, dj2, ba, hp⟩ := E.vals
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45, q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, q60, q61, q62, q63, q64, q65, q66, q67, q68, q69, q70, q71, q72, q73, q74, q75, q76, q77, q78, q79, q80⟩ := E.facts
  have hI : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr X (nextA .Sched d) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (prevA .Sched d) 0#u64) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) d) (L.nodeAt X (L.cpu X) (rqOff p)) d) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) (inqA d) = L.mem X (inqA d) := by simp (disch := assumption) only [mem_wr_ne']
  have hA : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr X (nextA .Sched d) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (prevA .Sched d) 0#u64) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) d) (L.nodeAt X (L.cpu X) (rqOff p)) d) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) (inqA d) (L.mem X (inqA d) ||| sched.Q_QUEUED)) (affA d) =
      L.cpu (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr X (nextA .Sched d) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (prevA .Sched d) 0#u64) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) d) (L.nodeAt X (L.cpu X) (rqOff p)) d) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) (inqA d) (L.mem X (inqA d) ||| sched.Q_QUEUED)) := by
    simp (disch := assumption) only [mem_wr_ne', L.cpu_wr]; exact E.haff
  apply eq_of_spec_fd
  unfold sched.enqueue
  rw [eq_of_spec_fd (sched.queued.spec (L := L) X d), E.hq]
  simp only [ne_eq, eq_self_iff_true, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
    bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) X d), E.haff]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Tcb.domain.spec (L := L) X d)]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Tcb.prio.spec (L := L) X d), E.hpr]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨off, hoff, ho1, ho2⟩ := spec_ex_fd (sched.rq_head_off.spec (L.mem X (domA d)) p hp)
  rw [hoff]; simp only [bind_ok, bind_tc_ok]; subst ho1
  rw [eq_of_spec_fd (sched.q_get.spec (L := L) X _ _), ho2]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (tcbqueue.Queue.is_empty.spec _)]
  simp only [bind_ok, bind_tc_ok, E.hh0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (spec_of_eq_fd (prepend_ne (L := L) X .Sched _ d E.hh0)) ?_
  rintro ⟨q1, s2⟩ hpp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpp
  refine WP.spec_bind (sched.q_set.spec (L := L) _ _ _ _) ?_
  rintro s3 hs3
  have e3 : s3 = (L.wr (L.wr (L.wr (L.wr (L.wr X (nextA .Sched d) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (prevA .Sched d) 0#u64) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) d) (L.nodeAt X (L.cpu X) (rqOff p)) d) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) := by
    simp only [nodeAt_wr] at hs3; rw [hs3, ho2]; all_goals rfl
  subst e3
  refine WP.spec_bind (sched.set_flag.spec (L := L) _ d _ true) ?_
  rintro s4 hs4
  have e4 : s4 = L.wr (L.wr (L.wr (L.wr (L.wr (L.wr X (nextA .Sched d) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (prevA .Sched d) 0#u64) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) d) (L.nodeAt X (L.cpu X) (rqOff p)) d) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) (inqA d) (L.mem X (inqA d) ||| sched.Q_QUEUED) := by
    rw [hs4, hI]; all_goals rfl
  subst e4
  rw [remote_queue_update_local (L := L) _ d hA]
  exact (WP.spec_ok _).2 rfl

/-- **`dequeue d` after `enqueue d` on a nonempty ready queue** restores every
queue word, the old head's `sched_prev` (F3: it was 0) and `d`'s `in_queues`
word (QUEUED was clear), and leaves `d`'s scheduler links 0. -/
theorem dequeue_enq_ne (hX : StoreExt st) {T : Set U64} {X : S} {d p : U64} (E : EnqNE (L := L) T X d p) :
    sched.dequeue st (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) d = ok (L.wr (L.wr X (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64) := by
  obtain ⟨n1, n2, n3, v1, v2, n6, n7, n8, n9, al1, al2, f1, f2, hdh, dj1, dj2, ba, hp⟩ := E.vals
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45, q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, q60, q61, q62, q63, q64, q65, q66, q67, q68, q69, q70, q71, q72, q73, q74, q75, q76, q77, q78, q79, q80⟩ := E.facts
  have yI : L.mem (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (inqA d) = L.mem X (inqA d) ||| sched.Q_QUEUED := by
    unfold enqNE; simp (disch := assumption) only [LawfulStore.mem_wr_same]
  have yA : L.mem (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (affA d) = L.cpu X := by unfold enqNE; simp (disch := assumption) only [mem_wr_ne']; exact E.haff
  have yD : L.mem (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (domA d) = L.mem X (domA d) := by unfold enqNE; simp (disch := assumption) only [mem_wr_ne']
  have yP : L.mem (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (prioA d) = p := by unfold enqNE; simp (disch := assumption) only [mem_wr_ne']; exact E.hpr
  have yC : L.cpu (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) = L.cpu X := by unfold enqNE; simp only [L.cpu_wr]
  have yN : ∀ o, L.nodeAt (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (L.cpu X) o = L.nodeAt X (L.cpu X) o := by intro o; unfold enqNE; simp only [nodeAt_wr]
  have yH : L.mem (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (L.nodeAt X (L.cpu X) (rqOff p)) = d := by unfold enqNE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  have yE : L.mem (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (L.nodeAt X (L.cpu X) (rqTailOff p)) = L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)) := by unfold enqNE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  have yPd : L.mem (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (prevA .Sched d) = 0#u64 := by unfold enqNE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  have yNd : L.mem (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (nextA .Sched d) = (L.mem X (L.nodeAt X (L.cpu X) (rqOff p))) := by unfold enqNE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  have hrm : removeF st (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) .Sched ⟨d, L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p))⟩ d = (⟨(L.mem X (L.nodeAt X (L.cpu X) (rqOff p))), L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p))⟩, (L.wr (L.wr (L.wr (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) 0#u64) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64)) := by
    unfold removeF; simp only [yNd, E.hed, and_false, ↓reduceIte]
  have zI : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) 0#u64) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64) (L.nodeAt X (L.cpu X) (rqOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) (inqA d) = L.mem X (inqA d) ||| sched.Q_QUEUED := by
    unfold enqNE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  have hfin : L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) 0#u64) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64) (L.nodeAt X (L.cpu X) (rqOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) (inqA d) (L.mem X (inqA d)) = L.wr (L.wr X (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64 := by
    unfold enqNE
    apply hX
    · intro x hx
      by_cases e0 : x = inqA d
      · subst e0; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e1 : x = (L.nodeAt X (L.cpu X) (rqTailOff p))
      · subst e1; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e2 : x = (L.nodeAt X (L.cpu X) (rqOff p))
      · subst e2; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e3 : x = prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))
      · subst e3; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same, E.hhp]
      by_cases e4 : x = nextA .Sched d
      · subst e4; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e5 : x = prevA .Sched d
      · subst e5; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      have e0' := Ne.symm e0
      have e1' := Ne.symm e1
      have e2' := Ne.symm e2
      have e3' := Ne.symm e3
      have e4' := Ne.symm e4
      have e5' := Ne.symm e5
      simp (disch := assumption) only [mem_wr_ne']
    · simp
    · simp
  have hQ : (decide ((L.mem X (inqA d) ||| sched.Q_QUEUED) &&& sched.Q_QUEUED ≠ 0#u64)) = true := by
    rw [or_qq_qq]; simp [qq_ne]
  apply eq_of_spec_fd
  unfold sched.dequeue
  rw [eq_of_spec_fd (sched.queued.spec (L := L) _ d), yI, hQ]
  simp only [↓reduceIte, bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) _ d), yA]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Tcb.domain.spec (L := L) _ d), yD]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (obj.Tcb.prio.spec (L := L) _ d), yP]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨off, hoff, ho1, ho2⟩ := spec_ex_fd (sched.rq_head_off.spec (L.mem X (domA d)) p hp)
  rw [hoff]; simp only [bind_ok, bind_tc_ok]; subst ho1
  rw [eq_of_spec_fd (sched.q_get.spec (L := L) _ _ _), ho2, yN, yN, yH, yE]; simp only [bind_ok, bind_tc_ok]
  refine WP.spec_bind (spec_of_eq_fd (tcbqueue.remove.ok (L := L) _ .Sched _ d)) ?_
  rintro ⟨q1, s1⟩ hpp
  rw [hrm] at hpp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpp.symm
  refine WP.spec_bind (sched.q_set.spec (L := L) _ _ _ _) ?_
  rintro s2 hs2
  have e2 : s2 = (L.wr (L.wr (L.wr (L.wr (L.wr (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) 0#u64) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64) (L.nodeAt X (L.cpu X) (rqOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) := by
    simp only [nodeAt_wr, yN] at hs2; rw [hs2, ho2]; all_goals rfl
  subst e2
  refine WP.spec_bind (sched.set_flag.spec (L := L) _ d _ false) ?_
  rintro s3 hs3
  have e3 : s3 = L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (enqNE (L := L) X d (L.nodeAt X (L.cpu X) (rqOff p)) (L.nodeAt X (L.cpu X) (rqTailOff p))) (prevA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) 0#u64) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64) (L.nodeAt X (L.cpu X) (rqOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqOff p)))) (L.nodeAt X (L.cpu X) (rqTailOff p)) (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)))) (inqA d) (L.mem X (inqA d)) := by
    rw [hs3, zI, or_andn_qq _ E.hq]; all_goals rfl
  subst e3
  refine WP.spec_bind (tcbqueue.Queue.is_empty.spec _) ?_
  rintro b rfl
  have hb : decide ((L.mem X (L.nodeAt X (L.cpu X) (rqOff p))) = 0#u64) = false := by simp [E.hh0]
  rw [hb]
  exact (WP.spec_ok _).2 hfin
end


/-! ## `schedule` from `CHOOSE_NEW` after the fault (m58 handoff (c)) -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- `schedule` after the new thread is switched to: the action back to
`RESUME_CURRENT`, `switch_sched_context`, the reprogram check, `send_pending`
(the same calls as the end of `fastpath.switch_to`). -/
def schedTail (s3 : S) (a2 : A) : Result (S × A) := do
  let s4 ← sched.set_action st s3 sched.ACTION_RESUME_CURRENT
  let (s5, a3) ← sched.switch_sched_context st ar s4 a2
  let c ← st.cur_cpu s5
  let i ← obj.node_get st s5 c layout.node.REPROGRAM
  let (s6, a4) ←
    if i != 0#u64
    then
      do
      let (s7, a5) ← sched.set_next_interrupt st ar s5 a3
      let s8 ← obj.node_set st s7 c layout.node.REPROGRAM 0#u64
      ok (s8, a5)
    else ok (s5, a3)
  smp.send_pending st ar s6 a4

theorem cn_bne_resume : (sched.ACTION_CHOOSE_NEW != sched.ACTION_RESUME_CURRENT) = true := by
  unfold sched.ACTION_CHOOSE_NEW sched.ACTION_RESUME_CURRENT; decide

/-- **`schedule` with the action `CHOOSE_NEW`** (after the fault's
`reply_push`): nothing due (`awaken_none`), one domain
(`check_domain_time_one`), the current thread not schedulable (it is
BlockedOnReply), the domain time not exhausted: `choose_thread`, then
`schedTail`. -/
theorem schedule_cn (s : S) (a : A)
    (hT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) <
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (hR : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime s))
    (ha : L.actionW s = sched.ACTION_CHOOSE_NEW)
    (hns : sched.is_schedulable st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)) = ok false)
    {v : U64} (hdt : sched.domain_time st s = ok v) (hv : v ≠ 0#u64) :
    sched.schedule st ar s a =
      (do
        let (s3, a2) ← sched.choose_thread st ar s a
        schedTail (st := st) ar s3 a2) := by
  unfold sched.schedule
  rw [awaken_none ar s a hT hR]; simp only [bind_ok, uncurry_apply_pair]
  rw [check_domain_time_one]; simp only [bind_ok]
  rw [eq_of_spec_fd (sched.action.spec (L := L) s), ha]
  simp only [bind_ok, cn_bne_resume, ↓reduceIte]
  rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)]; simp only [bind_ok]
  rw [hns]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  unfold sched.schedule_choose_new_thread
  rw [hdt]; simp only [bind_ok, hv, ↓reduceIte]
  rfl

/-- **`choose_thread` picks the head of the highest nonempty queue** (one
domain): with the L1 word nonzero and `highest_prio` = `p`, it is
`switch_to_thread` of the head word of queue `p`. -/
theorem choose_thread_eq_pick (s : S) (a : A) {p : U64} (hp : p.val < 256)
    (hl1 : L.l1W s (L.cpu s) ≠ 0#u64) (hhp : sched.highest_prio st s 0#u64 = ok p) :
    sched.choose_thread st ar s a =
      sched.switch_to_thread st ar s a (L.mem s (L.nodeAt s (L.cpu s) (rqOff p))) := by
  unfold sched.choose_thread
  rw [if_neg num_domains_one]; simp only [bind_ok]
  rw [L.cur_cpu_eq]; simp only [bind_ok]
  rw [bitmap_dom_one]; simp only [bind_ok]
  rw [eq_of_spec_fd l1_off_zero]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s _ _)]; simp only [bind_ok]
  have h1 : (L.mem s (L.nodeAt s (L.cpu s) l1Off) != 0#u64) = true := bne_iff_ne.2 hl1
  simp only [h1, ↓reduceIte]
  rw [hhp]; simp only [bind_ok]
  obtain ⟨off, hoff, ho1, -⟩ := spec_ex_fd (sched.rq_head_off.spec 0#u64 p hp)
  rw [hoff]; simp only [bind_ok]; subst ho1
  rw [eq_of_spec_fd (sched.q_get.spec (L := L) s _ _)]; simp only [bind_ok]

end

end Fl4Proofs.P1
