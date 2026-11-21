/-
P3 (DESIGN.md §9), scheduler: **the domain switch of
`schedule_choose_new_thread`** (KENTRY-PLAN.md sch2 (b)), the pieces both
sides compute when the domain time is 0 (after DomainScheduleSetStart, the
spec's `domain_set_start` sets `domain_time := 0`).

* `DomListOK`: l4v's `valid_domain_list` (DetSchedDomainTime_AI, `rt`) and
  every entry's domain 0 (FL4 is built with one domain; l4v's own note on
  `valid_domain_list_2`: "domains in the domain list should also be ≤
  maxDomain"). [J]: no invariant carries it yet (l4v:
  `valid_domain_list`, kept by every kernel step, `next_domain_valid_domain_list`,
  `domain_set_start_valid_domain_list_inv`, ...).
* `nextDomain_eq`: with FL4's two-entry table (`DomRel`: length 2) the
  index is 0 and the start index 0 (`DomListOK.idx0` / `start0`: the last
  entry is the end marker, the start entry is not), so `next_domain` goes
  back to entry 0: index 0, domain 0, the entry's duration, a timer
  reprogram; the work-unit reset is an extended op (none at `Z = Unit`).
* `next_domain_eq`: FL4's `next_domain` from a state whose `DOM_SCHED_IDX`
  and `DOM_SCHED_START` words are 0 and whose entry 1 has duration 0 (as
  `DomRel` of a `DomListOK` state gives, `next_domain_words`): the index 0,
  the reprogram flag, `WORK_UNITS := 0`, `CUR_DOMAIN := 0` and
  `DOMAIN_TIME :=` entry 0's duration (`ndS`).
-/
import Fl4Proofs.P3.ScScheduleTop
import Fl4Proofs.P3.DomDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section Spec
open Fl4Spec

/-- **The domain schedule's invariant**: l4v's `valid_domain_list`
(DetSchedDomainTime_AI, `rt`) and FL4's one domain (every entry's domain
0). [J] (see the module docstring). -/
structure DomListOK (σ : State Unit) : Prop where
  /-- One active entry and the reserved end marker at least. -/
  len : 1 < σ.domainList.length
  /-- Time can only be 0 in the end marker. -/
  zero : ∀ e ∈ σ.domainList, e.2 = 0 → e.1 = 0
  start : σ.domainStartIndex < σ.domainList.length
  /-- The start entry is not an end marker. -/
  startNE : σ.domainList[σ.domainStartIndex]? ≠ some domainEndMarker
  /-- The last entry is the end marker. -/
  last : σ.domainList[σ.domainList.length - 1]? = some domainEndMarker
  /-- The index never reaches the final end marker. -/
  idx : σ.domainIndex < σ.domainList.length - 1
  /-- FL4's one domain (`numDomains = 1`). -/
  dom : ∀ e ∈ σ.domainList, e.1 = 0

theorem DomListOK.idx0 {σ : State Unit} (h : DomListOK σ) (hl : σ.domainList.length = 2) : σ.domainIndex = 0 := by
  have := h.idx; omega

theorem DomListOK.last1 {σ : State Unit} (h : DomListOK σ) (hl : σ.domainList.length = 2) :
    σ.domainList[1]? = some domainEndMarker := by
  have := h.last; rw [hl] at this; exact this

theorem DomListOK.start0 {σ : State Unit} (h : DomListOK σ) (hl : σ.domainList.length = 2) :
    σ.domainStartIndex = 0 := by
  have h1 := h.start
  rw [hl] at h1
  by_contra hne
  have e : σ.domainStartIndex = 1 := by omega
  exact h.startNE (by rw [e]; exact h.last1 hl)

/-- The spec's state after `next_domain` from a `DomListOK` state with
two entries (`nextDomain_eq`). -/
def ndSt (σ : State Unit) (t : Word) : State Unit :=
  { σ with domainIndex := 0, curDomain := 0, domainTime := t, reprogramTimer := true }

/-- **`next_domain` with two entries** goes back to entry 0. -/
theorem nextDomain_eq {σ : State Unit} (hl : σ.domainList.length = 2) (hV : DomListOK σ) {d : DomainDuration}
    (e0 : σ.domainList[0]? = some (0, d)) :
    nextDomain (Z := Unit) σ = ({((), ndSt σ (ucast 64 d))}, False) := by
  have hi := hV.idx0 hl
  have hs := hV.start0 hl
  have h1 := hV.last1 hl
  unfold nextDomain
  rw [Notif.nd_bind_one (m := NonDet.modify _) rfl, doExtendedOp_unit]
  simp only [hi, Nat.zero_add, h1, the, ite_true, hs, e0, ndSt]

theorem ucast_ofNat56 {n : Nat} (h : n < 2 ^ 56) : ucast 64 (BitVec.ofNat 56 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [ucast, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem dom_eq (s : S) (i : U64) :
    sched.dom_sched_domain st s i = ok (L.mem s (ksW (L.ksb s) (entOff i))) := by
  unfold sched.dom_sched_domain
  rw [show layout.ks.DOM_SCHEDULE = ok 192#u64 by unfold layout.ks.DOM_SCHEDULE layout.WORD; rfl]
  simp only [lift, bind_ok, ks_get_eq]; rfl

theorem set_reprogram_eq (s : S) :
    sched.set_reprogram st s = ok (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64) := by
  have h : sched.set_reprogram st s ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64 ⦄ :=
    Sched.sched.set_reprogram.spec' s
  revert h
  cases sched.set_reprogram st s <;> simp [WP.spec_ok, WP.spec_vis, WP.spec_div]

/-- FL4's state after `next_domain` (`next_domain_eq`): `DOM_SCHED_IDX := 0`,
the reprogram flag, `WORK_UNITS := 0`, `CUR_DOMAIN := 0`,
`DOMAIN_TIME := t`. -/
def ndS (s : S) (t : U64) : S :=
  L.wr (L.wr (L.wr (L.wr (L.wr s (ksW (L.ksb s) 24#u64) 0#u64)
    (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64) (ksW (L.ksb s) 40#u64) 0#u64)
    (ksW (L.ksb s) 8#u64) 0#u64) (ksW (L.ksb s) 16#u64) t

/-- A node word is no kernel-global word below 256. -/
theorem mem_node_ks {T : Set U64} (s : S) (hN : P1.NodePlaced st T s (L.cpu s)) {o : U64} (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (v : U64) {k : U64} (hk : k.val < 256) (hk8 : k.val % 8 = 0) :
    L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (ksW (L.ksb s) k) = L.mem s (ksW (L.ksb s) k) := by
  have hf := hN.fits
  have hal := hN.align
  simp only [P1.LawfulStore.nodeBase] at hf hal
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  refine L.mem_wr_ne (P1.nodeAt_aligned hN ho h8) (ksW_al hkf hka hk hk8) ?_
  rw [P1.nodeAt_val hN ho, ksW_val (by omega)]
  simp only [P1.LawfulStore.nodeBase]; omega

/-- **FL4's `next_domain`** from index and start words 0 and an entry 1 of
duration 0: back to entry 0, whose domain word is 0. -/
theorem next_domain_eq {T : Set U64} (s : S) (hN : P1.NodePlaced st T s (L.cpu s))
    (h24 : L.mem s (ksW (L.ksb s) 24#u64) = 0#u64) (h32 : L.mem s (ksW (L.ksb s) 32#u64) = 0#u64)
    (hd1 : L.mem s (ksW (L.ksb s) (durOff 1#u64)) = 0#u64)
    (he0 : L.mem s (ksW (L.ksb s) (entOff 0#u64)) = 0#u64) :
    sched.next_domain st s = ok (ndS (L := L) s (L.mem s (ksW (L.ksb s) (durOff 0#u64)))) := by
  have hf : (L.ksb s).val + 13568 + (L.cpu s).val * 4288 + 4288 ≤ 2 ^ 64 := hN.fits
  have hal : ((L.ksb s).val + 13568 + (L.cpu s).val * 4288) % 8 = 0 := hN.align
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  have e1 : core.num.U64.wrapping_add (0#u64 : U64) 1#u64 = 1#u64 := rfl
  have hen : (entOff 0#u64).val = 192 := entOff_val (by decide)
  have hdn : (durOff 0#u64).val = 200 := durOff_val (by decide)
  have kI : layout.ks.DOM_SCHED_IDX = 24#u64 := by unfold layout.ks.DOM_SCHED_IDX; rfl
  have kS : layout.ks.DOM_SCHED_START = 32#u64 := by unfold layout.ks.DOM_SCHED_START; rfl
  have kW : layout.ks.WORK_UNITS = 40#u64 := by unfold layout.ks.WORK_UNITS; rfl
  have kC : layout.ks.CUR_DOMAIN = 8#u64 := by unfold layout.ks.CUR_DOMAIN; rfl
  have kD : layout.ks.DOMAIN_TIME = 16#u64 := by unfold layout.ks.DOMAIN_TIME; rfl
  have n12 : ¬ (1#u64 ≥ 2#u64) := by scalar_tac
  unfold sched.next_domain
  simp only [kI, kS, kW, kC, kD, ks_get_eq, bind_ok, lift, h24, e1, nds_eq, n12, if_false, dur_eq, hd1, ite_true,
    h32, ks_set_eq, set_reprogram_eq, dom_eq]
  try simp only [L.ksb_wr, L.cpu_wr]
  have hR : (L.nodeAt (L.wr s (ksW (L.ksb s) 24#u64) 0#u64) (L.cpu s) layout.node.REPROGRAM) =
      L.nodeAt s (L.cpu s) layout.node.REPROGRAM := Sched.nodeAt_ksb (L.ksb_wr _ _ _) _ _
  rw [hR]
  -- the entry words of the state after the first three writes
  have hrd : ∀ k : U64, k.val < 256 → k.val % 8 = 0 → k.val ≠ 24 → k.val ≠ 40 →
      L.mem (L.wr (L.wr (L.wr s (ksW (L.ksb s) 24#u64) 0#u64) (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
        (ksW (L.ksb s) 40#u64) 0#u64) (ksW (L.ksb s) k) = L.mem s (ksW (L.ksb s) k) := by
    intro k hk hk8 n24 n40
    have hN1 : P1.NodePlaced st T (L.wr s (ksW (L.ksb s) 24#u64) 0#u64)
        (L.cpu (L.wr s (ksW (L.ksb s) 24#u64) 0#u64)) := by rw [L.cpu_wr]; exact hN.wr
    rw [mem_ks_ne _ _ hkf hka (by decide) (by decide) hk hk8 (by simpa using n40.symm)]
    have := mem_node_ks (L.wr s (ksW (L.ksb s) 24#u64) 0#u64) hN1 (o := layout.node.REPROGRAM)
      (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) 1#u64 hk hk8
    simp only [L.ksb_wr, L.cpu_wr, hR] at this
    rw [this, mem_ks_ne _ _ hkf hka (by decide) (by decide) hk hk8 (by simpa using n24.symm)]
  rw [hrd _ (by rw [hen]; decide) (by rw [hen]) (by rw [hen]; decide) (by rw [hen]; decide), he0,
    hrd _ (by rw [hdn]; decide) (by rw [hdn]) (by rw [hdn]; decide) (by rw [hdn]; decide)]
  rfl

/-- **The words `next_domain_eq` needs, from `DomRel`** of a `DomListOK`
state whose index is related to the `DOM_SCHED_IDX` word, and the duration
it installs: the spec's `ucast` of entry 0's duration. -/
theorem next_domain_words {m : U64 → U64} {kb : U64} {σ : Fl4Spec.State Unit} (hD : DomRel m kb σ)
    (hV : DomListOK σ) (hidx : (m (ksW kb 24#u64)).val = σ.domainIndex) :
    m (ksW kb 24#u64) = 0#u64 ∧ m (ksW kb 32#u64) = 0#u64 ∧ m (ksW kb (durOff 1#u64)) = 0#u64 ∧
      m (ksW kb (entOff 0#u64)) = 0#u64 ∧
      σ.domainList[0]? = some ((0 : Fl4Spec.Domain), (BitVec.ofNat 56 (m (ksW kb (durOff 0#u64))).val : Fl4Spec.DomainDuration)) ∧
      Fl4Spec.ucast 64 (BitVec.ofNat 56 (m (ksW kb (durOff 0#u64))).val) = (m (ksW kb (durOff 0#u64))).bv := by
  obtain ⟨hl, hent, hst⟩ := hD
  have hi := hV.idx0 hl
  have hs := hV.start0 hl
  obtain ⟨l0, d0, u0, -⟩ := hent 0#u64 (by decide)
  obtain ⟨l1, d1, u1, z1⟩ := hent 1#u64 (by decide)
  have hdom0 : (BitVec.ofNat 8 (m (ksW kb (entOff 0#u64))).val : Fl4Spec.Domain) = 0 :=
    hV.dom _ (List.mem_of_getElem? l0)
  have he0 : m (ksW kb (entOff 0#u64)) = 0#u64 := by
    apply UScalar.eq_of_val_eq
    have := congrArg BitVec.toNat hdom0
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt d0] at this
    simpa using this
  have hm1 := hV.last1 hl
  rw [show σ.domainList[1]? = σ.domainList[(1#u64 : U64).val]? from rfl, l1] at hm1
  have hd1' : (BitVec.ofNat 56 (m (ksW kb (durOff 1#u64))).val : Fl4Spec.DomainDuration) = 0 := by
    have := congrArg Prod.snd (Option.some.inj hm1); exact this
  have hd1 : m (ksW kb (durOff 1#u64)) = 0#u64 := by
    apply UScalar.eq_of_val_eq
    have := congrArg BitVec.toNat hd1'
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt u1] at this
    simpa using this
  refine ⟨UScalar.eq_of_val_eq (by rw [hidx, hi]; rfl), UScalar.eq_of_val_eq (by rw [← hst, hs]; rfl), hd1, he0,
    by have h := l0; rw [hdom0] at h; exact h, ?_⟩
  rw [ucast_ofNat56 u0]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (m (ksW kb (durOff 0#u64))).bv.isLt

end

end

end Fl4Proofs.P3
