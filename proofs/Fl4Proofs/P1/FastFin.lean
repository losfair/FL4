/-
# The accepted fault fast path: `finish` (FL4 #56, m60)

KENTRY-PLAN m59's open list (c1)–(c4):

* (c1) `set_vm_root` reads only the thread's VTABLE slot, the kernel root
  word and the ASID table / pool words (`VmOff`), so it commutes with any
  write elsewhere (`set_vm_root_wr`, `set_vm_root_wrs`) and returns its
  store unchanged (`set_vm_root_ok_s`);
* (c2) after `enqueue d` with `d` of priority `p` at least the highest
  marked priority, `highest_prio` is `p` and the L1 word is set
  (`highest_prio_enq`, from P1's `sched.enqueue.ready` and
  `sched.highest_prio.spec`);
* (c3) the empty-queue case of F3: `enqueue d` sets the bitmap bits of `p`
  (`enqueue_e`) and `dequeue d` clears them again, restoring every word
  (`dequeue_enq_e`, from the empty queue `(0, 0)`, its clear L2 bit and the
  L1 bit iff the group's L2 word is set, `EnqE`);
* (c4) both paths end equal: `fault_fin_tail` (the general `finish` after
  `possible_switch_to` = the fast path's `switch_to`, for any enqueue whose
  dequeue restores the state), `fault_fin_gen` / `fault_fin` (both queue
  cases, from the reads `FinReads`), **`fault_same`** (an accepted
  `fastpath.fault` run ends where `handle_fault` + `finish` ends, as states
  under `StoreExt`, given the general path's reads `FaultOK`).
-/
import Fl4Proofs.P1.FastSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## (c1) `set_vm_root` past writes it does not read -/

/-- The address of word `hi` of the ASID table (P3 `Vs.atA`). -/
def atAF (ksb hi : U64) : U64 :=
  core.num.U64.wrapping_add ksb (core.num.U64.wrapping_add 288000#u64 (core.num.U64.wrapping_mul hi 8#u64))
/-- The address of word `lo` of the ASID pool at `p` (P3 `Vs.peA`). -/
def peAF (p lo : U64) : U64 := core.num.U64.wrapping_add p (core.num.U64.wrapping_mul lo 8#u64)
/-- The thread's VTABLE slot. -/
def vtA (t : U64) : U64 := core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_VTABLE layout.cte.SIZE)
/-- The kernel root word. -/
def krA (s : S) : U64 := core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT

@[step] theorem asid_table_base_fs : layout.ks.ASID_TABLE ⦃ v => v = 288000#u64 ⦄ := by
  unfold layout.ks.ASID_TABLE layout.MAX_NODES fl4_abi.config.MAX_NUM_NODES
  simp only [show ¬ ((64#u64 : U64) > 64#u64) by decide, ↓reduceIte]
  step*

theorem asid_table_eq (s : S) (hi : U64) :
    vspace.asid_table st s hi = ok (L.mem s (atAF (L.ksb s) (hi &&& 2047#u64))) := by
  apply eq_of_spec_fd
  unfold vspace.asid_table obj.ks_get
  have hN : vspace.N_ASID_POOLS = 2048#u64 := by unfold vspace.N_ASID_POOLS; rfl
  rw [hN]
  step*
  subst_vars
  congr 4
  apply UScalar.eq_of_val_eq
  simp_all [UScalar.val_and]

/-- The ASID table and pool words are aligned and not `A` (only the words
`find_asid` can read: table word `hi < 2048`, pool word `lo < 512`; m61: the
m60 form quantified over every `hi` / `lo`, which covers every aligned
address and so made `TabOff` false for every aligned `A`). -/
def TabOff (s : S) (A : U64) : Prop :=
  ∀ hi : U64, hi.val < 2048 → (Aligned (atAF (L.ksb s) hi) ∧ A ≠ atAF (L.ksb s) hi) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      Aligned (peAF (L.mem s (atAF (L.ksb s) hi)) lo) ∧ A ≠ peAF (L.mem s (atAF (L.ksb s) hi)) lo

theorem and2047_lt (i : U64) : (i &&& 2047#u64).val < 2048 := by
  rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem and511_lt (i : U64) : (i &&& 511#u64).val < 512 := by
  rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- **What `set_vm_root t` reads is not the word `A`** (aligned words only:
the VTABLE slot's two words, the kernel root, the ASID table and pools). -/
structure VmOff (s : S) (t A : U64) : Prop where
  hA : Aligned A
  sl0 : Aligned (vtA t) ∧ A ≠ vtA t
  sl1 : Aligned (core.num.U64.wrapping_add (vtA t) 8#u64) ∧ A ≠ core.num.U64.wrapping_add (vtA t) 8#u64
  kr : Aligned (krA (L := L) s) ∧ A ≠ krA (L := L) s
  tab : TabOff (L := L) s A

theorem find_asid_wr {s : S} {A v : U64} (hA : Aligned A) (hT : TabOff (L := L) s A) (asid : U64) :
    vspace.find_asid st (L.wr s A v) asid = vspace.find_asid st s asid := by
  unfold vspace.find_asid
  congr 1; funext i
  rw [asid_table_eq, asid_table_eq, L.ksb_wr]
  obtain ⟨⟨h1, h2⟩, h3⟩ := hT (i &&& 2047#u64) (and2047_lt i)
  rw [mem_wr_ne' hA h1 h2]
  by_cases hp : L.mem s (atAF (L.ksb s) (i &&& 2047#u64)) = 0#u64
  · simp only [hp, bind_ok, ↓reduceIte]
  · simp only [hp, bind_ok, ↓reduceIte, lift, L.read_eq]
    obtain ⟨h4, h5⟩ := h3 (asid &&& 511#u64) (and511_lt asid) hp
    unfold peAF at h4 h5
    rw [mem_wr_ne' hA h4 h5]

theorem find_vspace_for_asid_wr {s : S} {A v : U64} (hA : Aligned A) (hT : TabOff (L := L) s A) (asid : U64) :
    vspace.find_vspace_for_asid st (L.wr s A v) asid = vspace.find_vspace_for_asid st s asid := by
  unfold vspace.find_vspace_for_asid; rw [find_asid_wr hA hT]

theorem kernel_root_wr {s : S} {A v : U64} (hA : Aligned A) (h : Aligned (krA (L := L) s) ∧ A ≠ krA (L := L) s) :
    vspace.kernel_root st (L.wr s A v) = vspace.kernel_root st s := by
  unfold vspace.kernel_root obj.ks_get
  simp only [L.ks_base_eq, bind_ok, lift, L.read_eq, L.ksb_wr]
  unfold krA at h
  rw [mem_wr_ne' hA h.1 h.2]

theorem cap_wr {s : S} {A v : U64} (sl : U64) (hA : Aligned A) (h0 : Aligned sl ∧ A ≠ sl)
    (h1 : Aligned (core.num.U64.wrapping_add sl 8#u64) ∧ A ≠ core.num.U64.wrapping_add sl 8#u64) :
    obj.Slot.cap st sl (L.wr s A v) = obj.Slot.cap st sl s := by
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, mem_wr_ne' hA h0.1 h0.2, mem_wr_ne' hA h1.1 h1.2]

theorem slot_vt (t : U64) : obj.Tcb.slot t layout.tcb.SLOT_VTABLE = ok (vtA t) := by
  simp [obj.Tcb.slot, lift, vtA]

variable {A : Type _} (ar : machine.Arch A)

theorem set_kernel_vm_root_wr {s : S} {X v : U64} (a : A) (hX : Aligned X)
    (h : Aligned (krA (L := L) s) ∧ X ≠ krA (L := L) s) :
    vspace.set_kernel_vm_root st ar (L.wr s X v) a =
      (vspace.set_kernel_vm_root st ar s a) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  unfold vspace.set_kernel_vm_root
  rw [kernel_root_wr hX h]
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok]

/-- **(c1) `set_vm_root` commutes with a write it does not read.** -/
theorem set_vm_root_wr {s : S} {X v : U64} (a : A) (t : U64) (h : VmOff (L := L) s t X) :
    vspace.set_vm_root st ar (L.wr s X v) a t =
      (vspace.set_vm_root st ar s a t) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  unfold vspace.set_vm_root
  rw [slot_vt]; simp only [bind_ok]
  rw [cap_wr _ h.hA h.sl0 h.sl1]
  simp only [bind_tc_eq, Std.bind_assoc]
  congr 1; funext c
  have K := set_kernel_vm_root_wr (L := L) ar (v := v) a h.hA h.kr
  cases c
  all_goals try exact K
  rename_i ptr b asid
  cases b
  · exact K
  · simp only [↓reduceIte]
    rw [find_vspace_for_asid_wr h.hA h.tab]
    simp only [bind_tc_eq, Std.bind_assoc]
    congr 1; funext r
    rcases r with r1 | e
    · by_cases e1 : r1 = ptr
      · simp only [e1, ↓reduceIte, bind_tc_eq, Std.bind_assoc, bind_ok]
      · simp only [e1, ↓reduceIte]; exact K
    · exact K

theorem VmOff.wr {s : S} {t X B w : U64} (hX : VmOff (L := L) s t X) (hB : VmOff (L := L) s t B) :
    VmOff (L := L) (L.wr s B w) t X := by
  refine ⟨hX.hA, hX.sl0, hX.sl1, by unfold krA; rw [L.ksb_wr]; exact hX.kr, fun hi hhi => ?_⟩
  rw [L.ksb_wr]
  obtain ⟨⟨b1, b2⟩, -⟩ := hB.tab hi hhi
  rw [mem_wr_ne' hB.hA b1 b2]
  exact hX.tab hi hhi

/-- A sequence of writes. -/
def wrs (s : S) : List (U64 × U64) → S
  | [] => s
  | x :: l => wrs (L.wr s x.1 x.2) l

/-- **(c1) `set_vm_root` commutes with a sequence of writes it does not read.** -/
theorem set_vm_root_wrs (a : A) (t : U64) :
    ∀ (l : List (U64 × U64)) (x : U64 × U64) (s : S), (∀ y ∈ x :: l, VmOff (L := L) s t y.1) →
      vspace.set_vm_root st ar (wrs (L := L) s (x :: l)) a t =
        (vspace.set_vm_root st ar s a t) >>= fun r => ok (wrs (L := L) r.1 (x :: l), r.2) := by
  intro l
  induction l with
  | nil => intro x s h; simp only [wrs]; exact set_vm_root_wr ar a t (h x (by simp))
  | cons y l ih =>
    intro x s h
    have h0 := h x (by simp)
    have h1 : ∀ z ∈ y :: l, VmOff (L := L) (L.wr s x.1 x.2) t z.1 := fun z hz => (h z (by simp [hz])).wr h0
    show vspace.set_vm_root st ar (wrs (L := L) (L.wr s x.1 x.2) (y :: l)) a t = _
    rw [ih y _ h1, set_vm_root_wr ar a t h0]
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
    rfl

theorem set_kernel_vm_root_ok_s {s : S} {a : A} {r : S × A} (h : vspace.set_kernel_vm_root st ar s a = ok r) :
    r.1 = s := by
  unfold vspace.set_kernel_vm_root at h
  obtain ⟨k, -, h⟩ := bind_eq_ok h
  obtain ⟨a1, -, h⟩ := bind_eq_ok h
  have h2 := spec_of_eq_fd h; rw [WP.spec_ok] at h2; rw [← h2]

/-- `set_vm_root` returns its store unchanged. -/
theorem set_vm_root_ok_s {s : S} {a : A} {t : U64} {r : S × A} (h : vspace.set_vm_root st ar s a t = ok r) :
    r.1 = s := by
  unfold vspace.set_vm_root at h
  rw [slot_vt] at h; simp only [bind_ok] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  cases c
  all_goals try exact set_kernel_vm_root_ok_s ar h
  rename_i ptr b asid
  cases b
  · exact set_kernel_vm_root_ok_s ar h
  · simp only [↓reduceIte] at h
    obtain ⟨x, -, h⟩ := bind_eq_ok h
    rcases x with r1 | e
    · by_cases e1 : r1 = ptr
      · simp only [e1, ↓reduceIte] at h
        obtain ⟨a1, -, h⟩ := bind_eq_ok h
        have h2 := spec_of_eq_fd h; rw [WP.spec_ok] at h2; rw [← h2]
      · simp only [e1, ↓reduceIte] at h; exact set_kernel_vm_root_ok_s ar h
    · exact set_kernel_vm_root_ok_s ar h

end

/-! ## (c2) `highest_prio` after the enqueue -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- **(c2) After `enqueue d`, `highest_prio` is `d`'s priority** when that
priority is at least every marked one (`is_highest_prio`, checked by the fast
path), and the L1 word is set. -/
theorem highest_prio_enq {X Y : S} {d p : U64} {Q : U64 → List U64} (hT : TcbPlaced T) (hd : d ∈ T)
    (hpr : L.mem X (prioA d) = p) (hp : p.val < 256) (hN : NodePlaced st T X (L.cpu X))
    (haff : L.mem X (affA d) = L.cpu X) (hRQ : ReadyQueues st T X (L.cpu X) Q)
    (hnq : (L.mem X (inqA d) &&& sched.Q_QUEUED) = 0#u64) (hdq : ∀ p' : U64, p'.val < 256 → d ∉ Q p')
    (hhi : sched.is_highest_prio st X 0#u64 p = ok true) (hY : sched.enqueue st X d = ok Y)
    (hNY : NodePlaced st T Y (L.cpu X)) (hcY : L.cpu Y = L.cpu X) :
    sched.highest_prio st Y 0#u64 = ok p ∧ L.l1W Y (L.cpu Y) ≠ 0#u64 := by
  have E := sched.enqueue.ready (L := L) X d Q hT hd (by rw [hpr]; exact hp) (by rw [haff]; exact hN) hN
    (by rw [haff]; exact hRQ) (fun _ => hdq)
  rw [hY, WP.spec_ok, haff, hpr] at E
  simp only [hnq, ne_eq, not_true_eq_false, ↓reduceIte] at E
  obtain ⟨-, hB⟩ := E
  rw [hcY]
  have hNE : (Function.update Q p (d :: Q p)) p ≠ [] := by simp
  have hl1 : L.l1W Y (L.cpu X) ≠ 0#u64 := by
    have hb := (hB.l2 p hp).2 hNE
    have hw : L.l2W Y (L.cpu X) (p.val / 64) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hb⟩
    have hl := (hB.l1 (p.val / 64) (by omega)).2 ⟨by omega, hw⟩
    exact (ne_zero_iff_bit _).2 ⟨_, by omega, hl⟩
  refine ⟨?_, hl1⟩
  have hNY' : NodePlaced st T Y (L.cpu Y) := by rw [hcY]; exact hNY
  have hB' : BitmapOK st Y (L.cpu Y) (fun p' => Function.update Q p (d :: Q p) p' ≠ []) := by rw [hcY]; exact hB
  obtain ⟨q, hq, hq1, hq2, hq3⟩ := spec_ex_fd (sched.highest_prio.spec (L := L) Y 0#u64 _ hNY' hB' (by rw [hcY]; exact hl1))
  rw [hq]
  have hpq : p.val ≤ q.val := hq3 p hp hNE
  have hqp : q.val ≤ p.val := by
    by_cases e : q = p
    · rw [e]
    · rw [Function.update_of_ne e] at hq2
      obtain ⟨-, hBX⟩ := hRQ
      have hb := (hBX.l2 q hq1).2 hq2
      have hw : L.l2W X (L.cpu X) (q.val / 64) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hb⟩
      have hl := (hBX.l1 (q.val / 64) (by omega)).2 ⟨by omega, hw⟩
      have hlX : L.l1W X (L.cpu X) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hl⟩
      obtain ⟨h, hh, hh1, -, hh3⟩ := spec_ex_fd (sched.highest_prio.spec (L := L) X 0#u64 _ hN hBX hlX)
      have hqh := hh3 q hq1 hq2
      unfold sched.is_highest_prio at hhi
      rw [bitmap_dom_one, L.cur_cpu_eq] at hhi
      simp only [bind_ok] at hhi
      rw [eq_of_spec_fd l1_off_zero] at hhi
      simp only [bind_ok] at hhi
      rw [eq_of_spec_fd (obj.node_get.spec (L := L) X _ _)] at hhi
      simp only [bind_ok] at hhi
      have hl1X : L.mem X (L.nodeAt X (L.cpu X) l1Off) ≠ 0#u64 := hlX
      rw [if_neg hl1X, hh] at hhi
      simp only [bind_ok] at hhi
      have hge : p ≥ h := by simpa using hhi
      have : h.val ≤ p.val := hge
      omega
  exact congrArg ok (UScalar.eq_of_val_eq (by omega)).symm

end

/-! ## (c3) `enqueue` then `dequeue` on an empty ready queue (F3, empty case) -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- The state after `enqueue d` on an empty ready queue `p`: the L1 / L2
bitmap words `v1` / `v2`, `d`'s scheduler links 0, the queue `(d, d)`,
QUEUED set. -/
def enqE (X : S) (d p v1 v2 : U64) : S :=
  L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr X (L.nodeAt X (L.cpu X) l1Off) v1)
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) v2) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64)
    (L.nodeAt X (L.cpu X) (rqOff p)) d) (L.nodeAt X (L.cpu X) (rqTailOff p)) d)
    (inqA d) (L.mem X (inqA d) ||| sched.Q_QUEUED)

/-- What `enqueue d` then `dequeue d` on an empty ready queue read (F3, empty
case: the empty queue is `(0, 0)`, its L2 bit clear, the group's L1 bit set
iff the group's L2 word is nonzero — l4v `valid_queues`, `valid_bitmaps`). -/
structure EnqE (T : Set U64) (X : S) (d p : U64) : Prop where
  hT : TcbPlaced T
  hd : d ∈ T
  hN : NodePlaced st T X (L.cpu X)
  hp : p.val < 256
  hq : (L.mem X (inqA d) &&& sched.Q_QUEUED) = 0#u64
  hpr : L.mem X (prioA d) = p
  haff : L.mem X (affA d) = L.cpu X
  hh0 : L.mem X (L.nodeAt X (L.cpu X) (rqOff p)) = 0#u64
  he0 : L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)) = 0#u64
  hb2 : (L.l2W X (L.cpu X) (p.val / 64)).bv.getLsbD (p.val % 64) = false
  hb1 : (L.l1W X (L.cpu X)).bv.getLsbD (p.val / 64) = true ↔ L.l2W X (L.cpu X) (p.val / 64) ≠ 0#u64

theorem EnqE.vals {X : S} {d p : U64} (E : EnqE (L := L) T X d p) :
    (nextA .Sched d).val = d.val + 3480 ∧ (prevA .Sched d).val = d.val + 3488 ∧
    (L.nodeAt X (L.cpu X) (rqOff p)).val = L.nodeBase X (L.cpu X) + (168 + 16 * p.val) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)).val = L.nodeBase X (L.cpu X) + (176 + 16 * p.val) ∧
    (inqA d).val = d.val + 3592 ∧ (affA d).val = d.val + 3520 ∧ (domA d).val = d.val + 3432 ∧
    (prioA d).val = d.val + 3448 ∧
    (L.nodeAt X (L.cpu X) l1Off).val = L.nodeBase X (L.cpu X) + 128 ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))).val = L.nodeBase X (L.cpu X) + (136 + 8 * (3 - p.val / 64)) ∧
    d.val % 4096 = 0 ∧ d.val + 4096 ≤ 2 ^ 64 ∧
    (d.val + 4096 ≤ L.nodeBase X (L.cpu X) ∨ L.nodeBase X (L.cpu X) + 4288 ≤ d.val) ∧
    L.nodeBase X (L.cpu X) % 8 = 0 ∧ p.val < 256 := by
  have hda := E.hT d E.hd
  have hp := E.hp
  have hg : p.val / 64 < 4 := by omega
  have r1 := rqOff_val E.hp
  have r2 := rqTailOff_val E.hp
  have v1 := nodeAt_val E.hN (off := rqOff p) (by omega)
  have v2 := nodeAt_val E.hN (off := rqTailOff p) (by omega)
  have v3 := nodeAt_val E.hN (off := l1Off) (by rw [l1Off_val]; omega)
  have v4 := nodeAt_val E.hN (off := l2Off (p.val / 64)) (by rw [l2Off_val hg]; omega)
  have n1 := nextA_val hda .Sched
  have n2 := prevA_val hda .Sched
  have n7 : (affA d).val = d.val + 3520 := by unfold affA; rw [tcb_wadd_val hda (by decide)]; rfl
  have n8 : (domA d).val = d.val + 3432 := by unfold domA; rw [tcb_wadd_val hda (by decide)]; rfl
  have n9 : (prioA d).val = d.val + 3448 := by unfold prioA; rw [tcb_wadd_val hda (by decide)]; rfl
  simp only [nextOff, prevOff] at n1 n2
  have o1 : (3480#u64 : U64).val = 3480 := rfl
  have o2 : (3488#u64 : U64).val = 3488 := rfl
  rw [o1] at n1; rw [o2] at n2
  rw [r1] at v1; rw [r2] at v2; rw [l1Off_val] at v3; rw [l2Off_val hg] at v4
  exact ⟨n1, n2, v1, v2, inqA_val hda, n7, n8, n9, v3, v4, hda.align, hda.fits, E.hN.disj d E.hd, E.hN.align, hp⟩

theorem EnqE.facts {X : S} {d p : U64} (E : EnqE (L := L) T X d p) :
    Aligned (nextA .Sched d) ∧
    Aligned (prevA .Sched d) ∧
    Aligned (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    Aligned (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    Aligned (inqA d) ∧
    Aligned (affA d) ∧
    Aligned (domA d) ∧
    Aligned (prioA d) ∧
    Aligned (L.nodeAt X (L.cpu X) l1Off) ∧
    Aligned (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (nextA .Sched d) ≠ (prevA .Sched d) ∧
    (nextA .Sched d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (nextA .Sched d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (nextA .Sched d) ≠ (inqA d) ∧
    (nextA .Sched d) ≠ (affA d) ∧
    (nextA .Sched d) ≠ (domA d) ∧
    (nextA .Sched d) ≠ (prioA d) ∧
    (nextA .Sched d) ≠ (L.nodeAt X (L.cpu X) l1Off) ∧
    (nextA .Sched d) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (prevA .Sched d) ≠ (nextA .Sched d) ∧
    (prevA .Sched d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (prevA .Sched d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (prevA .Sched d) ≠ (inqA d) ∧
    (prevA .Sched d) ≠ (affA d) ∧
    (prevA .Sched d) ≠ (domA d) ∧
    (prevA .Sched d) ≠ (prioA d) ∧
    (prevA .Sched d) ≠ (L.nodeAt X (L.cpu X) l1Off) ∧
    (prevA .Sched d) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (nextA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (prevA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (inqA d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (affA d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (domA d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (prioA d) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (L.nodeAt X (L.cpu X) l1Off) ∧
    (L.nodeAt X (L.cpu X) (rqOff p)) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (nextA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (prevA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (inqA d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (affA d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (domA d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (prioA d) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (L.nodeAt X (L.cpu X) l1Off) ∧
    (L.nodeAt X (L.cpu X) (rqTailOff p)) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (inqA d) ≠ (nextA .Sched d) ∧
    (inqA d) ≠ (prevA .Sched d) ∧
    (inqA d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (inqA d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (inqA d) ≠ (affA d) ∧
    (inqA d) ≠ (domA d) ∧
    (inqA d) ≠ (prioA d) ∧
    (inqA d) ≠ (L.nodeAt X (L.cpu X) l1Off) ∧
    (inqA d) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (affA d) ≠ (nextA .Sched d) ∧
    (affA d) ≠ (prevA .Sched d) ∧
    (affA d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (affA d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (affA d) ≠ (inqA d) ∧
    (affA d) ≠ (domA d) ∧
    (affA d) ≠ (prioA d) ∧
    (affA d) ≠ (L.nodeAt X (L.cpu X) l1Off) ∧
    (affA d) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (domA d) ≠ (nextA .Sched d) ∧
    (domA d) ≠ (prevA .Sched d) ∧
    (domA d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (domA d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (domA d) ≠ (inqA d) ∧
    (domA d) ≠ (affA d) ∧
    (domA d) ≠ (prioA d) ∧
    (domA d) ≠ (L.nodeAt X (L.cpu X) l1Off) ∧
    (domA d) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (prioA d) ≠ (nextA .Sched d) ∧
    (prioA d) ≠ (prevA .Sched d) ∧
    (prioA d) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (prioA d) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (prioA d) ≠ (inqA d) ∧
    (prioA d) ≠ (affA d) ∧
    (prioA d) ≠ (domA d) ∧
    (prioA d) ≠ (L.nodeAt X (L.cpu X) l1Off) ∧
    (prioA d) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (nextA .Sched d) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (prevA .Sched d) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (inqA d) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (affA d) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (domA d) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (prioA d) ∧
    (L.nodeAt X (L.cpu X) l1Off) ≠ (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (nextA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (prevA .Sched d) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (L.nodeAt X (L.cpu X) (rqOff p)) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (L.nodeAt X (L.cpu X) (rqTailOff p)) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (inqA d) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (affA d) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (domA d) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (prioA d) ∧
    (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) ≠ (L.nodeAt X (L.cpu X) l1Off) := by
  obtain ⟨n1, n2, v1, v2, n6, n7, n8, n9, v3, v4, al1, f1, dj1, ba, hp⟩ := E.vals
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold Aligned; omega)
    | (intro e; have := congrArg UScalar.val e; omega)

theorem prepend_e (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : U64) (h : q.head = 0#u64) :
    tcbqueue.prepend st s l q t =
      ok (({ head := t, «end» := t } : tcbqueue.Queue), L.wr (L.wr s (nextA l t) 0#u64) (prevA l t) 0#u64) := by
  unfold tcbqueue.prepend
  rw [eq_of_spec_fd (tcbqueue.Queue.is_empty.spec q)]
  simp only [bind_ok, bind_tc_ok, h, decide_true, ↓reduceIte]
  rw [eq_of_spec_fd (tcbqueue.set_next.spec (L := L) s l t _)]; simp only [bind_ok, bind_tc_ok]
  rw [eq_of_spec_fd (tcbqueue.set_prev.spec (L := L) _ l t _)]; simp only [bind_ok, bind_tc_ok]

/-- **(c3) `enqueue d` on an empty ready queue**: the bitmap bits of `p` set,
`d` alone in the queue. -/
theorem enqueue_e {X : S} {d p : U64} (E : EnqE (L := L) T X d p) : ∃ v1 v2 : U64,
    (∀ i, v1.bv.getLsbD i = ((L.l1W X (L.cpu X)).bv.getLsbD i || decide (i = p.val / 64))) ∧
    (∀ i, v2.bv.getLsbD i = ((L.l2W X (L.cpu X) (p.val / 64)).bv.getLsbD i || decide (i = p.val % 64))) ∧
    sched.enqueue st X d = ok (enqE (L := L) X d p v1 v2) := by
  obtain ⟨n1, n2, v1, v2, n6, n7, n8, n9, v3, v4, al1, f1, dj1, ba, hp⟩ := E.vals
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45, q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, q60, q61, q62, q63, q64, q65, q66, q67, q68, q69, q70, q71, q72, q73, q74, q75, q76, q77, q78, q79, q80, q81, q82, q83, q84, q85, q86, q87, q88, q89, q90, q91, q92, q93, q94, q95, q96, q97, q98, q99⟩ := E.facts
  obtain ⟨X1, hX1, w1, w2, hX1e, hw1, hw2⟩ :=
    spec_ex_fd (sched.add_to_bitmap.spec (L := L) X (L.cpu X) (L.mem X (domA d)) p hp)
  refine ⟨w1, w2, hw1, fun i => ?_, ?_⟩
  · rw [hw2 i]; unfold LawfulStore.l2W; simp (disch := assumption) only [mem_wr_ne']
  subst hX1e
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
  simp only [bind_ok, bind_tc_ok, E.hh0, decide_true, ↓reduceIte]
  rw [hX1]; simp only [bind_ok, bind_tc_ok]
  refine WP.spec_bind (spec_of_eq_fd (prepend_e (L := L) _ .Sched _ d (by simp [E.hh0]))) ?_
  rintro ⟨q1, s2⟩ hpp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpp
  refine WP.spec_bind (sched.q_set.spec (L := L) _ _ _ _) ?_
  rintro s3 hs3
  simp only [nodeAt_wr] at hs3
  rw [ho2] at hs3
  subst hs3
  refine WP.spec_bind (sched.set_flag.spec (L := L) _ d _ true) ?_
  rintro s4 hs4
  have hI : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr X (L.nodeAt X (L.cpu X) l1Off) w1)
      (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) w2) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64)
      (L.nodeAt X (L.cpu X) (rqOff p)) d) (L.nodeAt X (L.cpu X) (rqTailOff p)) d) (inqA d) = L.mem X (inqA d) := by
    simp (disch := assumption) only [mem_wr_ne']
  rw [hI] at hs4
  simp only [↓reduceIte] at hs4
  subst hs4
  have hA : L.mem (enqE (L := L) X d p w1 w2) (affA d) = L.cpu (enqE (L := L) X d p w1 w2) := by
    unfold enqE; simp (disch := assumption) only [mem_wr_ne', L.cpu_wr]; exact E.haff
  unfold enqE at hA
  rw [remote_queue_update_local (L := L) _ d hA]
  exact (WP.spec_ok _).2 rfl

theorem bv_ext_ff {x y : U64} (h : ∀ i, x.bv.getLsbD i = y.bv.getLsbD i) : x = y := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi; exact h i

/-- **(c3) `dequeue d` after `enqueue d` on an empty ready queue** restores
every queue and bitmap word and `d`'s `in_queues` word, and leaves `d`'s
scheduler links 0. -/
theorem dequeue_enq_e (hX : StoreExt st) {X : S} {d p : U64} (E : EnqE (L := L) T X d p) {v1 v2 : U64}
    (hv1 : ∀ i, v1.bv.getLsbD i = ((L.l1W X (L.cpu X)).bv.getLsbD i || decide (i = p.val / 64)))
    (hv2 : ∀ i, v2.bv.getLsbD i = ((L.l2W X (L.cpu X) (p.val / 64)).bv.getLsbD i || decide (i = p.val % 64))) :
    sched.dequeue st (enqE (L := L) X d p v1 v2) d =
      ok (L.wr (L.wr X (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64) := by
  obtain ⟨n1, n2, w1, w2, n6, n7, n8, n9, w3, w4, al1, f1, dj1, ba, hp⟩ := E.vals
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45, q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, q60, q61, q62, q63, q64, q65, q66, q67, q68, q69, q70, q71, q72, q73, q74, q75, q76, q77, q78, q79, q80, q81, q82, q83, q84, q85, q86, q87, q88, q89, q90, q91, q92, q93, q94, q95, q96, q97, q98, q99⟩ := E.facts
  have yI : L.mem (enqE (L := L) X d p v1 v2) (inqA d) = L.mem X (inqA d) ||| sched.Q_QUEUED := by
    unfold enqE; simp (disch := assumption) only [LawfulStore.mem_wr_same]
  have yA : L.mem (enqE (L := L) X d p v1 v2) (affA d) = L.cpu X := by
    unfold enqE; simp (disch := assumption) only [mem_wr_ne']; exact E.haff
  have yD : L.mem (enqE (L := L) X d p v1 v2) (domA d) = L.mem X (domA d) := by
    unfold enqE; simp (disch := assumption) only [mem_wr_ne']
  have yP : L.mem (enqE (L := L) X d p v1 v2) (prioA d) = p := by
    unfold enqE; simp (disch := assumption) only [mem_wr_ne']; exact E.hpr
  have yN : ∀ o, L.nodeAt (enqE (L := L) X d p v1 v2) (L.cpu X) o = L.nodeAt X (L.cpu X) o := by
    intro o; unfold enqE; simp only [nodeAt_wr]
  have yH : L.mem (enqE (L := L) X d p v1 v2) (L.nodeAt X (L.cpu X) (rqOff p)) = d := by
    unfold enqE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  have yE : L.mem (enqE (L := L) X d p v1 v2) (L.nodeAt X (L.cpu X) (rqTailOff p)) = d := by
    unfold enqE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  have hQ : (decide ((L.mem X (inqA d) ||| sched.Q_QUEUED) &&& sched.Q_QUEUED ≠ 0#u64)) = true := by
    rw [or_qq_qq]; simp [qq_ne]
  have hrm : removeF st (enqE (L := L) X d p v1 v2) .Sched ⟨d, d⟩ d = (⟨0#u64, 0#u64⟩,
      L.wr (L.wr (enqE (L := L) X d p v1 v2) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64) := by
    unfold removeF; simp
  -- the L2 word comes back
  have hw2 : ∀ i, ((v2.bv.getLsbD i && !decide (i = p.val % 64))) = (L.l2W X (L.cpu X) (p.val / 64)).bv.getLsbD i := by
    intro i; rw [hv2 i]
    by_cases e : i = p.val % 64
    · subst e; simp [E.hb2]
    · simp [e]
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
  simp only [nodeAt_wr, yN, ho2] at hs2
  subst hs2
  refine WP.spec_bind (sched.set_flag.spec (L := L) _ d _ false) ?_
  rintro s3 hs3
  have zI : L.mem (L.wr (L.wr (L.wr (L.wr (enqE (L := L) X d p v1 v2) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64)
      (L.nodeAt X (L.cpu X) (rqOff p)) 0#u64) (L.nodeAt X (L.cpu X) (rqTailOff p)) 0#u64) (inqA d) =
      L.mem X (inqA d) ||| sched.Q_QUEUED := by
    unfold enqE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  simp only [Bool.false_eq_true, ↓reduceIte] at hs3
  rw [zI, or_andn_qq _ E.hq] at hs3
  subst hs3
  refine WP.spec_bind (tcbqueue.Queue.is_empty.spec _) ?_
  rintro b rfl
  simp only [decide_true, ↓reduceIte]
  refine WP.spec_mono (sched.remove_from_bitmap.spec (L := L) _ _ _ p hp) ?_
  rintro s4 ⟨u2, hu2, hs4⟩
  simp only [nodeAt_wr, LawfulStore.cpu_wr, yN] at hu2 hs4
  have hm2 : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (enqE (L := L) X d p v1 v2) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64)
      (L.nodeAt X (L.cpu X) (rqOff p)) 0#u64) (L.nodeAt X (L.cpu X) (rqTailOff p)) 0#u64) (inqA d) (L.mem X (inqA d)))
      (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) = v2 := by
    unfold enqE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
  rw [hm2] at hu2
  have hU2 : u2 = L.l2W X (L.cpu X) (p.val / 64) := bv_ext_ff fun i => by rw [hu2 i, hw2 i]
  subst hU2
  have hl2 : L.l2W X (L.cpu X) (p.val / 64) = L.mem X (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) := rfl
  have hl1 : L.l1W X (L.cpu X) = L.mem X (L.nodeAt X (L.cpu X) l1Off) := rfl
  by_cases hz : L.l2W X (L.cpu X) (p.val / 64) = 0#u64
  · rw [if_pos hz] at hs4
    obtain ⟨u1, rfl, hu1⟩ := hs4
    have hm1 : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (enqE (L := L) X d p v1 v2) (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64)
        (L.nodeAt X (L.cpu X) (rqOff p)) 0#u64) (L.nodeAt X (L.cpu X) (rqTailOff p)) 0#u64) (inqA d) (L.mem X (inqA d)))
        (L.nodeAt X (L.cpu X) (l2Off (p.val / 64))) (L.l2W X (L.cpu X) (p.val / 64))) (L.nodeAt X (L.cpu X) l1Off) = v1 := by
      unfold enqE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
    rw [hm1] at hu1
    have hb : (L.l1W X (L.cpu X)).bv.getLsbD (p.val / 64) = false := by
      cases h : (L.l1W X (L.cpu X)).bv.getLsbD (p.val / 64)
      · rfl
      · exact absurd hz (E.hb1.1 h)
    have hU1 : u1 = L.l1W X (L.cpu X) := bv_ext_ff fun i => by
      rw [hu1 i, hv1 i]
      by_cases e : i = p.val / 64
      · subst e; simp [hb]
      · simp [e]
    subst hU1
    rw [hl1, hl2]
    unfold enqE
    apply hX
    · intro x hx
      by_cases e0 : x = L.nodeAt X (L.cpu X) l1Off
      · subst e0; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e1 : x = L.nodeAt X (L.cpu X) (l2Off (p.val / 64))
      · subst e1; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e2 : x = L.nodeAt X (L.cpu X) (rqOff p)
      · subst e2; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same, E.hh0]
      by_cases e3 : x = L.nodeAt X (L.cpu X) (rqTailOff p)
      · subst e3; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same, E.he0]
      by_cases e4 : x = nextA .Sched d
      · subst e4; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e5 : x = prevA .Sched d
      · subst e5; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e6 : x = inqA d
      · subst e6; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      have e0' := Ne.symm e0
      have e1' := Ne.symm e1
      have e2' := Ne.symm e2
      have e3' := Ne.symm e3
      have e4' := Ne.symm e4
      have e5' := Ne.symm e5
      have e6' := Ne.symm e6
      simp (disch := assumption) only [mem_wr_ne']
    · simp
    · simp
  · rw [if_neg hz] at hs4
    subst hs4
    have hb : (L.l1W X (L.cpu X)).bv.getLsbD (p.val / 64) = true := E.hb1.2 hz
    have hV1 : v1 = L.l1W X (L.cpu X) := bv_ext_ff fun i => by
      rw [hv1 i]
      by_cases e : i = p.val / 64
      · subst e; simp [hb]
      · simp [e]
    subst hV1
    rw [hl1, hl2]
    unfold enqE
    apply hX
    · intro x hx
      by_cases e0 : x = L.nodeAt X (L.cpu X) l1Off
      · subst e0; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e1 : x = L.nodeAt X (L.cpu X) (l2Off (p.val / 64))
      · subst e1; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e2 : x = L.nodeAt X (L.cpu X) (rqOff p)
      · subst e2; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same, E.hh0]
      by_cases e3 : x = L.nodeAt X (L.cpu X) (rqTailOff p)
      · subst e3; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same, E.he0]
      by_cases e4 : x = nextA .Sched d
      · subst e4; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e5 : x = prevA .Sched d
      · subst e5; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      by_cases e6 : x = inqA d
      · subst e6; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
      have e0' := Ne.symm e0
      have e1' := Ne.symm e1
      have e2' := Ne.symm e2
      have e3' := Ne.symm e3
      have e4' := Ne.symm e4
      have e5' := Ne.symm e5
      have e6' := Ne.symm e6
      simp (disch := assumption) only [mem_wr_ne']
    · simp
    · simp

end

/-! ## (c4) `finish` after the fault: the two paths end equal -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

theorem ok_inj_ff {α : Type _} {x y : α} (h : (ok x : Result α) = ok y) : x = y := by
  have h2 := spec_of_eq_fd h; rw [WP.spec_ok] at h2; exact h2

theorem obj.Tcb.set_sched_next.ok (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_sched_next st t s v = ok (L.wr s (nextA .Sched t) v) := by
  have h := tcbqueue.set_next.spec (L := L) s .Sched t v
  unfold tcbqueue.set_next at h; exact eq_of_spec_fd h

theorem obj.Tcb.set_sched_prev.ok (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_sched_prev st t s v = ok (L.wr s (prevA .Sched t) v) := by
  have h := tcbqueue.set_prev.spec (L := L) s .Sched t v
  unfold tcbqueue.set_prev at h; exact eq_of_spec_fd h

theorem set_cur_thread_ok (s : S) (t : obj.Tcb) :
    sched.set_cur_thread st s t = ok (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) t) :=
  eq_of_spec_fd (sched.set_cur_thread.spec s t)

theorem set_action_ok (s : S) (v : U64) :
    sched.set_action st s v = ok (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) :=
  eq_of_spec_fd (sched.set_action.spec s v)

/-- The end of `fastpath.switch_to` after RESUME: `switch_sched_context`, the
reprogram check, `send_pending`, `activate_thread`. -/
def fastTail (s3 : S) (a1 : A) : Result (S × A) := do
  let (s4, a2) ← sched.switch_sched_context st ar s3 a1
  let c ← st.cur_cpu s4
  let i ← obj.node_get st s4 c layout.node.REPROGRAM
  let (s5, a3) ←
    if i != 0#u64
    then
      do
      let (s6, a4) ← sched.set_next_interrupt st ar s4 a2
      let s7 ← obj.node_set st s6 c layout.node.REPROGRAM 0#u64
      ok (s7, a4)
    else ok (s4, a2)
  let (s6, a4) ← smp.send_pending st ar s5 a3
  sched.activate_thread st ar s6 a4

/-- `schedule`'s end then `activate_thread` is the fast path's end. -/
theorem schedTail_act (S0 : S) (a0 : A) (g : S × A → Result (S × A))
    (hg : ∀ x : S × A, g x = sched.activate_thread st ar x.1 x.2) :
    Std.bind (schedTail (st := st) ar S0 a0) g =
      fastTail (st := st) ar (L.wr S0 (L.nodeAt S0 (L.cpu S0) layout.node.SCHED_ACTION)
        sched.ACTION_RESUME_CURRENT) a0 := by
  unfold schedTail fastTail
  rw [set_action_ok]
  simp only [bind_ok, bind_tc_eq, Std.bind_assoc]
  congr 1; funext x; obtain ⟨s4, a2⟩ := x
  try simp only [uncurry_apply_pair, bind_tc_eq, Std.bind_assoc]
  congr 1; funext c
  try simp only [bind_tc_eq, Std.bind_assoc]
  congr 1; funext i
  try simp only [bind_tc_eq, Std.bind_assoc]
  congr 1; funext y; obtain ⟨s5, a3⟩ := y
  try simp only [uncurry_apply_pair, bind_tc_eq, Std.bind_assoc]
  congr 1; funext z; obtain ⟨s6, a4⟩ := z
  try simp only [uncurry_apply_pair]
  exact hg _


/-- The fast path's end: from the state `U` after `unblock_sporadic`, the
handler's scheduler links cleared, `switch_to` (= `set_vm_root`, CUR_THREAD,
RESUME, then the common tail). -/
def fastFin (U : S) (a : A) (d : obj.Tcb) : Result (Bool × S × A) := do
  let s16 ← obj.Tcb.set_sched_next st d U 0#u64
  let s17 ← obj.Tcb.set_sched_prev st d s16 0#u64
  let (s18, a1) ← fastpath.switch_to st ar s17 a d
  ok (true, s18, a1)

/-- **(c4) The general `finish` after the fault ends where the fast path
does**, for any shape of the enqueue (`Y`, a sequence of writes from `U`
starting with the action word) whose dequeue restores the state up to the
handler's cleared links (`hD`) and from which `schedule` switches to the
handler (`hsch`); `set_vm_root` reads none of the words written (`hvY`, `hvn`,
`hvp`). -/
theorem fault_fin_tail (hX : StoreExt st) (U Y : S) (a : A) (d : obj.Tcb) (lY : List (U64 × U64))
    {sF : S} {aF : A}
    (hfast : fastFin (st := st) ar U a d = ok (true, sF, aF))
    (hpst : sched.possible_switch_to st (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d =
      sched.enqueue st (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d)
    (hY : sched.enqueue st (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d = ok Y)
    (hYw : Y = wrs (L := L) U ((actA (L := L) U, sched.ACTION_CHOOSE_NEW) :: lY))
    (hsch : sched.schedule st ar Y a =
      (do let (s3, a2) ← sched.switch_to_thread st ar Y a d; schedTail (st := st) ar s3 a2))
    (hD : sched.dequeue st Y d = ok (L.wr (L.wr (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)
      (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64))
    (hvY : ∀ y ∈ (actA (L := L) U, sched.ACTION_CHOOSE_NEW) :: lY, VmOff (L := L) U d y.1)
    (hvn : VmOff (L := L) U d (nextA .Sched d)) (hvp : VmOff (L := L) U d (prevA .Sched d))
    (haA : Aligned (actA (L := L) U)) (hnA : Aligned (nextA .Sched d)) (hpA : Aligned (prevA .Sched d))
    (hcA : Aligned (curA (L := L) U))
    (h1 : actA (L := L) U ≠ nextA .Sched d) (h2 : actA (L := L) U ≠ prevA .Sched d)
    (h3 : actA (L := L) U ≠ curA (L := L) U) :
    (do
      let s7 ← sched.possible_switch_to st (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d
      syscall.finish st ar s7 a) = ok (sF, aF) := by
  -- the fast side
  unfold fastFin at hfast
  rw [obj.Tcb.set_sched_next.ok] at hfast
  simp only [bind_ok] at hfast
  rw [obj.Tcb.set_sched_prev.ok] at hfast
  simp only [bind_ok] at hfast
  obtain ⟨⟨x1, x2⟩, hsw, hx⟩ := bind_eq_ok hfast
  try simp only at hx
  have hx' := ok_inj_ff hx
  simp only [Prod.mk.injEq, true_and] at hx'
  obtain ⟨rfl, rfl⟩ := hx'
  unfold fastpath.switch_to at hsw
  rw [show L.wr (L.wr U (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64 =
      wrs (L := L) U [(nextA .Sched d, 0#u64), (prevA .Sched d, 0#u64)] from rfl,
    set_vm_root_wrs ar a d [(prevA .Sched d, 0#u64)] (nextA .Sched d, 0#u64) U
      (by intro y hy; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact hvn
          · exact hvp)] at hsw
  simp only [bind_tc_eq, Std.bind_assoc] at hsw
  obtain ⟨⟨U', aV⟩, hv, -⟩ := bind_eq_ok hsw
  have hU' : U' = U := set_vm_root_ok_s ar hv
  rw [hU'] at hv
  rw [hv] at hsw
  simp only [bind_ok, wrs, uncurry_apply_pair] at hsw
  rw [set_cur_thread_ok] at hsw; simp only [bind_ok, uncurry_apply_pair] at hsw
  rw [set_action_ok] at hsw; simp only [bind_ok, uncurry_apply_pair] at hsw
  -- the general side
  rw [hpst, hY]; simp only [bind_ok]
  unfold syscall.finish
  rw [hsch]
  unfold sched.switch_to_thread
  rw [hYw, set_vm_root_wrs ar a d lY _ U hvY, hv]
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok, wrs, uncurry_apply_pair]
  rw [show wrs (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) lY = Y from by rw [hYw]; rfl, hD]
  simp only [bind_ok, uncurry_apply_pair]
  rw [set_cur_thread_ok]; simp only [bind_ok, uncurry_apply_pair]
  try simp only [bind_tc_eq]
  rw [schedTail_act ar]
  rotate_left
  · intro x; rfl
  simp only [nodeAt_wr, LawfulStore.cpu_wr] at hsw ⊢
  have key : L.wr (L.wr (L.wr (L.wr (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (nextA .Sched d) 0#u64)
      (prevA .Sched d) 0#u64) (curA (L := L) U) d) (actA (L := L) U) sched.ACTION_RESUME_CURRENT =
      L.wr (L.wr (L.wr (L.wr U (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64) (curA (L := L) U) d)
        (actA (L := L) U) sched.ACTION_RESUME_CURRENT := by
    rw [wr_comm hX U _ _ haA hnA h1, wr_comm hX _ _ _ haA hpA h2, wr_comm hX _ _ _ haA hcA h3,
      wr_wr hX _ _ _ haA]
  rw [key]
  exact hsw


/-! ### Reads past a sequence of writes -/

theorem mem_wrs_ne {r : U64} (hr : Aligned r) : ∀ (l : List (U64 × U64)) (s : S),
    (∀ x ∈ l, Aligned x.1 ∧ x.1 ≠ r) → L.mem (wrs (L := L) s l) r = L.mem s r := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons x l ih =>
    intro s h
    show L.mem (wrs (L := L) (L.wr s x.1 x.2) l) r = _
    rw [ih _ (fun y hy => h y (by simp [hy])), mem_wr_ne' (h x (by simp)).1 hr (h x (by simp)).2]

theorem cpu_wrs : ∀ (l : List (U64 × U64)) (s : S), L.cpu (wrs (L := L) s l) = L.cpu s := by
  intro l; induction l with
  | nil => intro s; rfl
  | cons x l ih => intro s; show L.cpu (wrs (L := L) (L.wr s x.1 x.2) l) = _; rw [ih]; simp

theorem nodeAt_wrs (c o : U64) : ∀ (l : List (U64 × U64)) (s : S),
    L.nodeAt (wrs (L := L) s l) c o = L.nodeAt s c o := by
  intro l; induction l with
  | nil => intro s; rfl
  | cons x l ih => intro s; show L.nodeAt (wrs (L := L) (L.wr s x.1 x.2) l) c o = _; rw [ih]; simp

theorem ksb_wrs : ∀ (l : List (U64 × U64)) (s : S), L.ksb (wrs (L := L) s l) = L.ksb s := by
  intro l; induction l with
  | nil => intro s; rfl
  | cons x l ih => intro s; show L.ksb (wrs (L := L) (L.wr s x.1 x.2) l) = _; rw [ih]; simp

theorem NodePlaced.wrs {T : Set U64} {c : U64} : ∀ (l : List (U64 × U64)) (s : S),
    NodePlaced st T s c → NodePlaced st T (wrs (L := L) s l) c := by
  intro l; induction l with
  | nil => intro s h; exact h
  | cons x l ih => intro s h; exact ih _ h.wr

theorem domain_time_eq (s : S) :
    sched.domain_time st s = ok (L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME)) := by
  unfold sched.domain_time obj.ks_get
  simp only [L.ks_base_eq, bind_ok, lift, L.read_eq]

/-- The words `schedule` reads from `CHOOSE_NEW` before it switches (one
domain), besides `awaken`'s (`NoDue`): the action word, the current thread
word, the current thread's state, DOMAIN_TIME. -/
def schedRd (X : S) : List U64 :=
  [actA (L := L) X, curA (L := L) X, stA (L.mem X (curA (L := L) X)),
   core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME]

/-- **Nothing due at `Y`** (what `awaken` reads, `schedule_cn`'s `hT` / `hR`):
the earliest timer is empty or later than `CUR_TIME`, the release queue is
empty or its head's SC not ready — what `schedulable_here` checked at the
entry (m61: m60 asked for TIMER_MIN = RELEASE_HEAD = 0, false wherever the
fast path accepts with a timer pending or a release queue nonempty). -/
def NoDue (Y : S) : Prop :=
  (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_TIME) <
        L.mem Y (tdA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN)))) ∧
  (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill Y (L.mem Y (scA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD))))
          (L.rhead Y (L.mem Y (scA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime Y))

/-- **(c4) `finish` after the fault, for an enqueue made of the writes `lW`**
(the general form of both queue cases): the reads `possible_switch_to`,
`schedule` and `choose_thread` make, at the state `X` with the action
`CHOOSE_NEW`. -/
theorem fault_fin_gen (hX : StoreExt st) {T : Set U64} (U X Y : S) (a : A) (d p : U64) {Q : U64 → List U64}
    (lW : List (U64 × U64)) (lA : List U64) (hlA : lW.map Prod.fst = lA) {sF : S} {aF : A}
    (hfast : fastFin (st := st) ar U a d = ok (true, sF, aF))
    (hXd : X = L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)
    (hsc : L.mem X (scA d) ≠ 0#u64) (hrq : (L.mem X (inqA d) &&& sched.Q_RELEASE) = 0#u64)
    (hdom : L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) = L.mem X (domA d))
    (haff : L.mem X (affA d) = L.cpu X)
    (hT : TcbPlaced T) (hd : d ∈ T) (hpr : L.mem X (prioA d) = p) (hp : p.val < 256)
    (hN : NodePlaced st T X (L.cpu X)) (hRQ : ReadyQueues st T X (L.cpu X) Q)
    (hnq : (L.mem X (inqA d) &&& sched.Q_QUEUED) = 0#u64) (hdq : ∀ p' : U64, p'.val < 256 → d ∉ Q p')
    (hhi : sched.is_highest_prio st X 0#u64 p = ok true)
    (hY : sched.enqueue st X d = ok Y) (hYw : Y = wrs (L := L) X lW)
    (hD : sched.dequeue st Y d = ok (L.wr (L.wr X (nextA .Sched d) 0#u64) (prevA .Sched d) 0#u64))
    (hH : L.mem Y (L.nodeAt X (L.cpu X) (rqOff p)) = d)
    (hND : NoDue (L := L) Y)
    (hns : ¬ (L.mem X (stA (L.mem X (curA (L := L) X))) = sched.TS_RUNNING ∨
      L.mem X (stA (L.mem X (curA (L := L) X))) = sched.TS_RESTART ∨
      L.mem X (stA (L.mem X (curA (L := L) X))) = sched.TS_RUNNING_VM))
    (hdt : L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME) ≠ 0#u64)
    (hrd : ∀ r ∈ schedRd (L := L) X, Aligned r ∧ ∀ w ∈ lA, Aligned w ∧ w ≠ r)
    (hvm : ∀ w ∈ actA (L := L) U :: lA, VmOff (L := L) U d w)
    (hvn : VmOff (L := L) U d (nextA .Sched d)) (hvp : VmOff (L := L) U d (prevA .Sched d))
    (haA : Aligned (actA (L := L) U)) (hnA : Aligned (nextA .Sched d)) (hpA : Aligned (prevA .Sched d))
    (hcA : Aligned (curA (L := L) U))
    (h1 : actA (L := L) U ≠ nextA .Sched d) (h2 : actA (L := L) U ≠ prevA .Sched d)
    (h3 : actA (L := L) U ≠ curA (L := L) U) :
    (do
      let s7 ← sched.possible_switch_to st (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d
      syscall.finish st ar s7 a) = ok (sF, aF) := by
  subst hXd
  have hrdW : ∀ r ∈ schedRd (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW), Aligned r ∧ ∀ x ∈ lW, Aligned x.1 ∧ x.1 ≠ r := fun r hr =>
    ⟨(hrd r hr).1, fun x hx => (hrd r hr).2 x.1 (hlA ▸ List.mem_map.2 ⟨x, hx, rfl⟩)⟩
  have rdY : ∀ r ∈ schedRd (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW), L.mem Y r = L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) r := fun r hr => by
    rw [hYw]; exact mem_wrs_ne (hrdW r hr).1 lW _ (hrdW r hr).2
  have eN : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) o := fun o => by
    rw [hYw, nodeAt_wrs, cpu_wrs]
  have eK : L.ksb Y = L.ksb (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) := by rw [hYw, ksb_wrs]
  have hAX : actA (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) = actA (L := L) U := by simp only [actA, nodeAt_wr, LawfulStore.cpu_wr]
  have hCX : curA (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) = curA (L := L) U := by simp only [curA, nodeAt_wr, LawfulStore.cpu_wr]
  have haX : L.actionW (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) = sched.ACTION_CHOOSE_NEW := by
    show L.mem _ (actA (L := L) _) = _
    rw [hAX, LawfulStore.mem_wr_same haA]
  have hpst := possible_switch_to_cn (L := L) hX _ d hsc hrq hdom haff haX (by rw [hAX]; exact haA)
  obtain ⟨hhp, hl1⟩ := highest_prio_enq (L := L) hT hd hpr hp hN haff hRQ hnq hdq hhi hY
    (by rw [hYw]; exact NodePlaced.wrs lW _ hN) (by rw [hYw, cpu_wrs])
  have m := fun r hr => rdY r hr
  have rA := m (actA (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (by simp [schedRd])
  have rC := m (curA (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (by simp [schedRd])
  have rS := m (stA (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (curA (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)))) (by simp [schedRd])
  have rD := m (core.num.U64.wrapping_add (L.ksb (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) layout.ks.DOMAIN_TIME) (by simp [schedRd])
  have hsch : sched.schedule st ar Y a =
      (do let (s3, a2) ← sched.switch_to_thread st ar Y a d; schedTail (st := st) ar s3 a2) := by
    rw [schedule_cn ar Y a hND.1 hND.2
      (by show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _; rw [eN]; exact rA.trans haX)
      (is_schedulable_not Y _ (by rw [eN]; rw [rC, rS]; exact hns))
      (domain_time_eq Y) (by rw [eK, rD]; exact hdt)]
    rw [choose_thread_eq_pick ar Y a hp hl1 hhp, eN, hH]
  exact fault_fin_tail ar hX U Y a d lW hfast hpst hY (by rw [hYw]; rfl) hsch hD
    (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hvm _ (by simp)
      · exact hvm _ (List.mem_cons_of_mem _ (hlA ▸ List.mem_map.2 ⟨y, hy, rfl⟩)))
    hvn hvp haA hnA hpA hcA h1 h2 h3


/-- The reads of `finish` after the fault common to both queue cases, at the
state `U` after `unblock_sporadic` (the action word then set to `CHOOSE_NEW`):
`possible_switch_to`'s (the handler has an SC, is outside the release queue,
in the current domain, on this core), the ready queues and the fast path's
`is_highest_prio`, `schedule`'s (nothing due, the current thread blocked, the
domain time left), and the addresses of the final writes. Each is a read at a
state the general path reaches (KENTRY-PLAN m60 (d) derives them from the entry
state). -/
structure FinCommon (T : Set U64) (U : S) (d p : U64) (Q : U64 → List U64) : Prop where
  hsc : L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (scA d) ≠ 0#u64
  hrq : (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (inqA d) &&& sched.Q_RELEASE) = 0#u64
  hdom : L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (core.num.U64.wrapping_add (L.ksb (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) layout.ks.CUR_DOMAIN) = L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (domA d)
  hRQ : ReadyQueues st T (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) Q
  hdq : ∀ p' : U64, p'.val < 256 → d ∉ Q p'
  hhi : sched.is_highest_prio st (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) 0#u64 p = ok true
  hns : ¬ (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (stA (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (curA (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)))) = sched.TS_RUNNING ∨
      L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (stA (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (curA (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)))) = sched.TS_RESTART ∨
      L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (stA (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (curA (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)))) = sched.TS_RUNNING_VM)
  hdt : L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (core.num.U64.wrapping_add (L.ksb (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) layout.ks.DOMAIN_TIME) ≠ 0#u64
  hvn : VmOff (L := L) U d (nextA .Sched d)
  hvp : VmOff (L := L) U d (prevA .Sched d)
  haA : Aligned (actA (L := L) U)
  hcA : Aligned (curA (L := L) U)
  h1 : actA (L := L) U ≠ nextA .Sched d
  h2 : actA (L := L) U ≠ prevA .Sched d
  h3 : actA (L := L) U ≠ curA (L := L) U

/-- **The reads of `finish` after the fault** (both queue cases, F3). -/
def FinReads (U : S) (d : U64) : Prop :=
  ∃ (T : Set U64) (p : U64) (Q : U64 → List U64), FinCommon (L := L) T U d p Q ∧
    ((EnqNE (L := L) T (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d p ∧
        NoDue (L := L) (enqNE (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p))) ∧
        (∀ r ∈ schedRd (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW), Aligned r ∧ ∀ w ∈ [nextA .Sched d, prevA .Sched d, prevA .Sched (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p))), (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)), (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p)), inqA d], Aligned w ∧ w ≠ r) ∧
        ∀ w ∈ actA (L := L) U :: [nextA .Sched d, prevA .Sched d, prevA .Sched (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p))), (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)), (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p)), inqA d], VmOff (L := L) U d w) ∨
     (EnqE (L := L) T (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d p ∧
        (∀ v1 v2 : U64, NoDue (L := L) (enqE (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d p v1 v2)) ∧
        (∀ r ∈ schedRd (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW), Aligned r ∧ ∀ w ∈ [(L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) l1Off), (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (l2Off (p.val / 64))), nextA .Sched d, prevA .Sched d, (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)), (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p)), inqA d], Aligned w ∧ w ≠ r) ∧
        ∀ w ∈ actA (L := L) U :: [(L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) l1Off), (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (l2Off (p.val / 64))), nextA .Sched d, prevA .Sched d, (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)), (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p)), inqA d], VmOff (L := L) U d w))

/-- **(c4) `finish` after the fault ends where the fast path does** (both
queue cases). -/
theorem fault_fin (hX : StoreExt st) (U : S) (a : A) (d : U64) {sF : S} {aF : A}
    (hfast : fastFin (st := st) ar U a d = ok (true, sF, aF)) (R : FinReads (L := L) U d) :
    (do
      let s7 ← sched.possible_switch_to st (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d
      syscall.finish st ar s7 a) = ok (sF, aF) := by
  obtain ⟨T, p, Q, C, hc⟩ := R
  rcases hc with ⟨E, hnd, hrd, hvm⟩ | ⟨E, hnd, hrd, hvm⟩
  · obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45, q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, q60, q61, q62, q63, q64, q65, q66, q67, q68, q69, q70, q71, q72, q73, q74, q75, q76, q77, q78, q79, q80⟩ := E.facts
    have hH : L.mem (enqNE (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p))) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)) = d := by
      unfold enqNE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
    exact fault_fin_gen ar hX U _ _ a d p
      [(nextA .Sched d, L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p))), (prevA .Sched d, 0#u64), (prevA .Sched (L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p))), d), ((L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)), d),
        ((L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p)), L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p))), (inqA d, L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (inqA d) ||| sched.Q_QUEUED)] _ rfl
      hfast rfl C.hsc C.hrq C.hdom E.haff E.hT E.hd E.hpr E.hp E.hN C.hRQ E.hq C.hdq C.hhi (enqueue_ne E) rfl
      (dequeue_enq_ne hX E) hH hnd C.hns C.hdt hrd hvm C.hvn C.hvp C.haA q0 q1 C.hcA C.h1 C.h2 C.h3
  · obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45, q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, q60, q61, q62, q63, q64, q65, q66, q67, q68, q69, q70, q71, q72, q73, q74, q75, q76, q77, q78, q79, q80, q81, q82, q83, q84, q85, q86, q87, q88, q89, q90, q91, q92, q93, q94, q95, q96, q97, q98, q99⟩ := E.facts
    obtain ⟨v1, v2, hv1, hv2, hY⟩ := enqueue_e E
    have hH : L.mem (enqE (L := L) (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) d p v1 v2) (L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)) = d := by
      unfold enqE; simp (disch := assumption) only [mem_wr_ne', LawfulStore.mem_wr_same]
    exact fault_fin_gen ar hX U _ _ a d p
      [((L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) l1Off), v1), ((L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (l2Off (p.val / 64))), v2), (nextA .Sched d, 0#u64), (prevA .Sched d, 0#u64), ((L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqOff p)), d), ((L.nodeAt (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW)) (rqTailOff p)), d),
        (inqA d, L.mem (L.wr U (actA (L := L) U) sched.ACTION_CHOOSE_NEW) (inqA d) ||| sched.Q_QUEUED)] _ rfl
      hfast rfl C.hsc C.hrq C.hdom E.haff E.hT E.hd E.hpr E.hp E.hN C.hRQ E.hq C.hdq C.hhi hY rfl
      (dequeue_enq_e hX E hv1 hv2) hH (hnd v1 v2) C.hns C.hdt hrd hvm C.hvn C.hvp C.haA q0 q1 C.hcA C.h1 C.h2 C.h3

end


/-! ## (c4) The accepted fault fast path ends where the general fault path does -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- The meeting state of m58's `fault_sync`: the handler `Running`. -/
def fS14 (S8 : S) (t dest r : U64) : S :=
  L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (stA dest) sched.TS_RUNNING

/-- **The reads of the general fault path** at the states it reaches, for an
accepted fast run from `s` (m58 `FaultReads`, m59 `UsOff`, m60 `FinReads`),
over the run's intermediate states. -/
def FaultOK (s : S) (a : A) (t : obj.Tcb) (n : U64) : Prop :=
  ∀ ptr badge dest r, FaultChecks st s t ptr badge dest r →
    ∀ (rb sent : U64) (S6 S7 S8 : S) (mi : msginfo.MessageInfo),
    msg.lookup_ipc_buffer st (epFast (L := L) (sfW (L := L) s t n) ptr dest) true dest = ok rb →
    faults.set_mrs_fault st ar (epFast (L := L) (sfW (L := L) s t n) ptr dest) a t dest rb = ok (sent, S6) →
    msginfo.MessageInfo.new fl4_abi.consts.fault.UnknownSyscall 0#u64 0#u64 sent = ok mi →
    msg.set_msg_info st S6 dest mi = ok S7 →
    obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8 →
    ∃ (T : Set U64) (rest : List U64) (sb : Nat), FaultReads (L := L) T s t n ptr dest r rest S6 S8 ∧
      UsOff (L := L) (fS14 (L := L) S8 t dest r) dest (actA (L := L) (fS14 (L := L) S8 t dest r)) sb ∧
      ∀ s15, endpoint.unblock_sporadic st (fS14 (L := L) S8 t dest r) dest = ok s15 →
        actA (L := L) s15 = actA (L := L) (fS14 (L := L) S8 t dest r) ∧ FinReads (L := L) s15 dest

/-- **(c4) `FastSame` for the fault fast path**: an accepted `fastpath.fault`
run ends exactly where the general `handle_fault` + `finish` ends (under
`StoreExt`, as states; the Arch value the same), given the general path's reads
(`FaultOK`). -/
theorem fault_same (hX : StoreExt st) {s : S} {a : A} {t : obj.Tcb} {n : U64} {sF : S} {aF : A}
    (h : fastpath.fault st ar s a t n = ok (true, sF, aF)) (hR : FaultOK (L := L) ar s a t n) :
    (do
      let (s2, a2) ← faults.handle_fault st ar s a t (error.Fault.UnknownSyscall n)
      syscall.finish st ar s2 a2) = ok (sF, aF) := by
  obtain ⟨ptr, badge, dest, r, hc, hfast⟩ := fault_acc st ar h
  rw [faultTail_eq] at hfast
  have hf0 := hfast
  unfold faultTail2 at hfast
  obtain ⟨rb, hbuf, h1⟩ := bind_eq_ok hfast
  obtain ⟨⟨sent, S6⟩, hmrs, h2⟩ := bind_eq_ok h1
  try simp only [uncurry_apply_pair] at h2
  obtain ⟨mi, hmi, h3⟩ := bind_eq_ok h2
  obtain ⟨S7, hS7, h4⟩ := bind_eq_ok h3
  obtain ⟨S8, hS8, -⟩ := bind_eq_ok h4
  obtain ⟨T, rest, sb, R, hU, hF⟩ := hR ptr badge dest r hc rb sent S6 S7 S8 mi hbuf hmrs hmi hS7 hS8
  obtain ⟨sl, x, y, g, gr, hsl, hcap, hG⟩ := hc.cap
  rw [faultTail2_eq ar _ a t dest r badge hbuf hmrs hmi hS7 hS8, faultTail3_eq] at hf0
  obtain ⟨s15, h15, hfin⟩ := bind_eq_ok hf0
  obtain ⟨hA15, FR⟩ := hF s15 h15
  rw [handle_fault_pre ar hX R.hT s a t n ptr badge dest r rest hsl hcap hG R.hE R.hq1 R.hst1 hbuf hmrs
      R.hR5 R.hR6 hmi hS7 hS8 R.hR8 hc.r0 R.hdt R.hR10c R.hR10f R.hR10a R.hR13s R.hR13c R.hR13a R.hR13d R.hR14c]
  have hA14 : actA (L := L) (fS14 (L := L) S8 t dest r) = actA (L := L) S8 := by
    unfold fS14 fS13 fS10; simp only [actA_wr]
  have hW : L.wr (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (actA (L := L) S8) sched.ACTION_CHOOSE_NEW)
      (stA dest) sched.TS_RUNNING =
      L.wr (fS14 (L := L) S8 t dest r) (actA (L := L) (fS14 (L := L) S8 t dest r)) sched.ACTION_CHOOSE_NEW := by
    rw [hA14]; unfold fS14; exact wr_comm hX _ _ _ R.haA R.hsA R.hAS
  have h15' : endpoint.unblock_sporadic st (fS14 (L := L) S8 t dest r) dest = ok s15 := h15
  rw [hW, unblock_sporadic_wr hX hU, h15']
  simp only [bind_ok, bind_tc_eq, Std.bind_assoc, uncurry_apply_pair]
  rw [← hA15]
  exact fault_fin ar hX s15 a dest hfin FR

end

end Fl4Proofs.P1
