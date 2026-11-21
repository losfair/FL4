/-
# The fault half of the entry's fast-path premise (FL4 #56, m60 (e))

`kernel_entry.entry_of4`'s `hF` [P] (`FastAcc` for every number) is split
into its two halves:

* the **fault half**, now proved (`usf_same`, `hus_same`, from FastFin's
  `fault_same`): a run of the entry where `fastpath.fault` answered ends where
  the general entry ends, given the general path's reads at the state where
  `fastpath.fault` is entered (`UsfOK`, `HusOK`, collected per entry state as
  `FastFaultOK`) and `StoreExt` [P];
* the **ReplyRecv half** `FastRRP` [P], unchanged in content: only the runs
  where `fastpath.reply_recv` answered (from the dispatch state after the
  `FAULT_IP` write and a passing `budget_ok`, P3's `KFrontB` / `FastRR`).

`FastAcc.of_split` puts them together and `kernel_entry.entry_of5` is
`entry_of4` with `hF` replaced by `StoreExt`, `FastFaultOK` and `FastRRP`.
-/
import Fl4Proofs.P1.FastFin
import Fl4Proofs.P1.QueueEntryGaps4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- The general path's reads for `unknown_syscall_fault s a n` (at the state
after a passing `budget_ok`, where `fastpath.fault` is entered). -/
def UsfOK (s : S) (a : A) (n : U64) : Prop :=
  ∀ s1 a1 t, syscall.budget_ok st ar s a = ok (true, s1, a1) → sched.cur_thread st s1 = ok t →
    FaultOK (L := L) ar s1 a1 t n

/-- **`unknown_syscall_fault` where the fault fast path answered is the general
one.** -/
theorem usf_same (hX : StoreExt st) {s : S} {a : A} {n : U64} {s' : S} {a' : A} (hF : UsfOK (L := L) ar s a n)
    (h : syscall.unknown_syscall_fault st ar s a n true = ok (true, s', a')) :
    syscall.unknown_syscall_fault st ar s a n false = ok (false, s', a') := by
  have h' := spec_of_eq_fd h
  clear h
  unfold syscall.unknown_syscall_fault at h' ⊢
  obtain ⟨⟨b, s1, a1⟩, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  try simp only [uncurry_apply_pair] at h'
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h' ⊢
    obtain ⟨⟨u, v⟩, -, h'⟩ := spec_bind_inv h'
    try simp only [uncurry_apply_pair] at h'
    rw [WP.spec_ok] at h'; simp at h'
  · simp only [↓reduceIte] at h' ⊢
    obtain ⟨t, et, h'⟩ := spec_bind_inv h'
    rw [et]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, Bool.false_eq_true]
    try simp only [↓reduceIte] at h'
    obtain ⟨⟨b1, s2, a2⟩, e2, h'⟩ := spec_bind_inv h'
    try simp only [uncurry_apply_pair] at h'
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte] at h'
      obtain ⟨⟨u, v⟩, -, h'⟩ := spec_bind_inv h'
      try simp only [uncurry_apply_pair] at h'
      obtain ⟨⟨u', v'⟩, -, h'⟩ := spec_bind_inv h'
      try simp only [uncurry_apply_pair] at h'
      rw [WP.spec_ok] at h'; simp at h'
    · simp only [↓reduceIte, WP.spec_ok] at h'
      simp only [Prod.mk.injEq, true_and] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hs := fault_same ar hX e2 (hF s1 a1 t e et)
      obtain ⟨⟨p1, p2⟩, ehf, hs⟩ := bind_eq_ok hs
      try simp only [uncurry_apply_pair] at hs
      rw [ehf]; simp only [bind_ok, uncurry_apply_pair]
      rw [hs]; simp only [bind_ok, uncurry_apply_pair]

/-- The general path's reads for `handle_unknown_syscall s a n`: wherever it
calls `unknown_syscall_fault` (after `debug_syscall` declined). -/
def HusOK (s : S) (a : A) (n : I64) : Prop :=
  ∀ t s1 a1, sched.cur_thread st s = ok t → syscall.debug_syscall st ar s a t n = ok (false, s1, a1) →
    UsfOK (L := L) ar s1 a1 (IScalar.hcast .U64 n)

/-- **`handle_unknown_syscall` where the fault fast path answered is the
general one.** -/
theorem hus_same (hX : StoreExt st) {s : S} {a : A} {n : I64} {s' : S} {a' : A} (hF : HusOK (L := L) ar s a n)
    (h : syscall.handle_unknown_syscall st ar s a n true = ok (true, s', a')) :
    syscall.handle_unknown_syscall st ar s a n false = ok (false, s', a') := by
  have h' := spec_of_eq_fd h
  clear h
  unfold syscall.handle_unknown_syscall at h' ⊢
  simp only [fl4_abi.config.PRINTING, fl4_abi.config.DEBUG_BUILD, fl4_abi.config.SET_TLS_BASE_SELF,
    ↓reduceIte, lift, bind_ok] at h' ⊢
  obtain ⟨t, et, h'⟩ := spec_bind_inv h'
  rw [et]; simp only [bind_ok, uncurry_apply_pair]
  by_cases h1 : n = fl4_abi.syscall.SysDebugPutChar
  · exfalso; simp only [if_pos h1] at h'
    revert h'
    repeat' (first
      | (refine spec_bind_imp (fun _ => ?_); try simp only [uncurry_eta_fd])
      | (refine spec_bind_imp' (fun _ => ?_); try simp only [uncurry_eta_fd]))
    intro h'; rw [WP.spec_ok] at h'; simp at h'
  simp only [if_neg h1] at h' ⊢
  by_cases h2 : n = fl4_abi.syscall.SysDebugDumpScheduler
  · exfalso; simp only [if_pos h2] at h'; rw [WP.spec_ok] at h'; simp at h'
  simp only [if_neg h2] at h' ⊢
  obtain ⟨⟨b, s1, a1⟩, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  try simp only [uncurry_apply_pair] at h'
  cases b
  swap
  · exfalso; simp only [↓reduceIte] at h'; rw [WP.spec_ok] at h'; simp at h'
  simp only [Bool.false_eq_true, ↓reduceIte] at h' ⊢
  have hU := hF t s1 a1 et e
  by_cases h3 : n = fl4_abi.syscall.SysSetTLSBase
  · exfalso; simp only [if_pos h3] at h'
    obtain ⟨⟨u, v⟩, -, h'⟩ := spec_bind_inv h'
    try simp only [uncurry_apply_pair] at h'
    rw [WP.spec_ok] at h'; simp at h'
  simp only [if_neg h3] at h' ⊢
  by_cases h4 : n = fl4_abi.syscall.SysVMEnter
  swap
  · simp only [if_neg h4] at h' ⊢; exact usf_same ar hX hU (eq_of_spec_fd h')
  simp only [if_pos h4] at h' ⊢
  obtain ⟨i, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  by_cases h5 : (i != 0#u64) = true
  swap
  · simp only [if_neg h5] at h' ⊢; exact usf_same ar hX hU (eq_of_spec_fd h')
  simp only [if_pos h5] at h' ⊢
  obtain ⟨i1, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  by_cases h6 : (i1 != 0#u64) = true
  swap
  · simp only [if_neg h6] at h' ⊢; exact usf_same ar hX hU (eq_of_spec_fd h')
  exfalso
  simp only [if_pos h6] at h'
  revert h'
  repeat' (first
    | (refine spec_bind_imp (fun _ => ?_); try simp only [uncurry_eta_fd])
    | (refine spec_bind_imp' (fun _ => ?_); try simp only [uncurry_eta_fd])
    | split)
  all_goals (intro h'; rw [WP.spec_ok] at h'; simp at h')

/-- **The fault half at an entry state**: the general path's reads wherever
`handle_syscall_fast` may enter `fastpath.fault` (after the `FAULT_IP` write:
the trap route and the out-of-range route). -/
def FastFaultOK (s : S) (a : A) (n : I64) : Prop :=
  ∀ t nx s1, sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    UsfOK (L := L) ar s1 a (IScalar.hcast .U64 n) ∧ HusOK (L := L) ar s1 a n

/-- **[P] The ReplyRecv half** of `FastAcc`: only the runs where
`fastpath.reply_recv` answered, from the dispatch state (the `FAULT_IP` write,
then a passing `budget_ok`; P3 `KFrontB` / `FastRR`). l4v counterpart:
`Fastpath_C`'s `fastpath_reply_recv` refines the slow path where it does not
fall back. -/
def FastRRP (s : S) (a : A) (n : I64) (P : S × A → Prop) : Prop :=
  ∀ t nx s1 s2 a2 s' a', sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    syscall.budget_ok st ar s1 a = ok (true, s2, a2) →
    fastpath.reply_recv st ar s2 a2 = ok (true, s', a') →
    syscall.handle_syscall_general st ar s a n ⦃ P ⦄ → P (s', a')

/-- **`FastAcc` from its two halves**: the fault half proved (`usf_same`,
`hus_same`) under `StoreExt` and the reads `FastFaultOK`, the ReplyRecv half
`FastRRP`. -/
theorem FastAcc.of_split (hX : StoreExt st) {s : S} {a : A} {n : I64} {P : S × A → Prop}
    (hF : FastFaultOK (L := L) ar s a n) (hR : FastRRP (st := st) ar s a n P) : FastAcc st ar s a n P := by
  intro hg s' a' e0
  have hgen : syscall.syscall st ar s a n false = ok (false, s', a') →
      syscall.handle_syscall_general st ar s a n = ok (s', a') := fun hs => by
    unfold syscall.handle_syscall_general; rw [hs]; simp only [bind_ok, uncurry_apply_pair]
  have e1 : syscall.syscall st ar s a n true = ok (true, s', a') := by
    unfold syscall.handle_syscall_fast at e0; exact e0
  have h' := spec_of_eq_fd e1
  clear e0
  have hsyn : syscall.syscall st ar s a n false = ok (false, s', a') ∨
      ∃ t nx s1 s2 a2, sched.cur_thread st s = ok t ∧ obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx ∧
        obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 ∧
        syscall.budget_ok st ar s1 a = ok (true, s2, a2) ∧ fastpath.reply_recv st ar s2 a2 = ok (true, s', a') := by
    unfold syscall.syscall at h' ⊢
    simp only [lift, bind_ok] at h' ⊢
    obtain ⟨t, et, h'⟩ := spec_bind_inv h'
    rw [et]; simp only [bind_ok, uncurry_apply_pair]
    obtain ⟨nx, enx, h'⟩ := spec_bind_inv h'
    rw [enx]; simp only [bind_ok, uncurry_apply_pair]
    obtain ⟨s1, es1, h'⟩ := spec_bind_inv h'
    rw [es1]; simp only [bind_ok, uncurry_apply_pair]
    obtain ⟨hU, hH⟩ := hF t nx s1 et enx es1
    obtain ⟨i1, e, h'⟩ := spec_bind_inv h'
    rw [e]; simp only [bind_ok, uncurry_apply_pair]
    by_cases c1 : (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
    · simp only [if_pos c1] at h' ⊢
      exact Or.inl (usf_same ar hX hU (eq_of_spec_fd h'))
    simp only [if_neg c1] at h' ⊢
    by_cases c2 : n < fl4_abi.syscall.SYSCALL_MIN
    · simp only [if_pos c2] at h' ⊢; exact Or.inl (hus_same ar hX hH (eq_of_spec_fd h'))
    simp only [if_neg c2] at h' ⊢
    by_cases c3 : n > fl4_abi.syscall.SYSCALL_MAX
    · simp only [if_pos c3] at h' ⊢; exact Or.inl (hus_same ar hX hH (eq_of_spec_fd h'))
    simp only [if_neg c3] at h' ⊢
    obtain ⟨⟨b, s2, a1⟩, e, h'⟩ := spec_bind_inv h'
    try simp only [uncurry_apply_pair] at h'
    cases b
    · exfalso; simp only [Bool.false_eq_true, ↓reduceIte] at h'
      obtain ⟨⟨u, v⟩, -, h'⟩ := spec_bind_inv h'
      try simp only [uncurry_apply_pair] at h'
      rw [WP.spec_ok] at h'; simp at h'
    simp only [↓reduceIte] at h'
    by_cases c4 : n = fl4_abi.syscall.SysReplyRecv
    · simp only [if_pos c4] at h'
      obtain ⟨⟨b1, s3, a2⟩, e2, h'⟩ := spec_bind_inv h'
      try simp only [uncurry_apply_pair] at h'
      cases b1
      · exfalso; simp only [Bool.false_eq_true, ↓reduceIte] at h'
        obtain ⟨⟨u, v⟩, -, h'⟩ := spec_bind_inv h'
        try simp only [uncurry_apply_pair] at h'
        obtain ⟨⟨u', v'⟩, -, h'⟩ := spec_bind_inv h'
        try simp only [uncurry_apply_pair] at h'
        rw [WP.spec_ok] at h'; simp at h'
      · simp only [↓reduceIte, WP.spec_ok, Prod.mk.injEq, true_and] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact Or.inr ⟨t, nx, s1, s2, a1, by first | exact et | rfl, by first | exact enx | rfl,
          by first | exact es1 | rfl, e, e2⟩
    · exfalso; simp only [if_neg c4] at h'
      obtain ⟨⟨u, v⟩, -, h'⟩ := spec_bind_inv h'
      try simp only [uncurry_apply_pair] at h'
      obtain ⟨⟨u', v'⟩, -, h'⟩ := spec_bind_inv h'
      try simp only [uncurry_apply_pair] at h'
      rw [WP.spec_ok] at h'; simp at h'
  rcases hsyn with hs | ⟨t, nx, s1, s2, a2, et, enx, es1, eb, er⟩
  · rw [hgen hs, WP.spec_ok] at hg; exact hg
  · exact hR t nx s1 s2 a2 s' a' et enx es1 eb er hg

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **Native kernel entries keep `EntryInv`**, `entry_of4` with its fast-path
premise `hF` [P] split (m60 (e)): the fault half discharged (`FastAcc.of_split`)
from `StoreExt` [P] and the general path's reads `FastFaultOK` [J] (each true
in reachable states, from the entry state's placement invariants: KENTRY-PLAN
m58–m60 (d)), the ReplyRecv half `FastRRP` [P] (unchanged). -/
theorem kernel_entry.entry_of5 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps4 st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hFt : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FastFaultOK (L := L) ar s a number)
    (hRR : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastRRP (st := st) ar s a number (fun r => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' r.1)) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry_of4 hA GF hσ s a hP h fun number hN =>
    FastAcc.of_split ar hX (hFt number hN) (hRR number hN)

end

end Fl4Proofs.P1
