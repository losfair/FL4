/-
# The fast paths decline without a trace (FL4 #56, m57)

fastpath.rs: "Their preconditions are checked with reads only, so a fast
path that declines (`false`) leaves the state to the general path
untouched." In the extraction every `false` exit of `fastpath.fault`,
`fastpath.reply_recv_found` and `fastpath.reply_recv` is literally
`ok (false, s, a)` at the entry state; the write sequence only starts once
every check has passed and it ends in `ok (true, _, _)`.

* `fault_decline`, `reply_recv_found_decline`, `reply_recv_decline`:
  `= ok (false, s', a')` gives `(s', a') = (s, a)`.
* `usf_decline`, `hus_decline`, `syscall_decline`: a run of the entry with
  the fast paths enabled that ends `false` (no fast path answered) ends
  exactly as the run with them disabled.
* `FastAcc` [P]: `FastAgree` asked only of the runs where a fast path
  answered (`handle_syscall_fast … = ok (true, s', a')`).
  `FastAgree.of_acc`: with total store and Arch (P0), `FastAcc` gives
  `FastAgree` (the fast entry is total, P0 `handle_syscall_fast.p0`; a
  declined run is the general run by `syscall_decline`).

Everything here is structural: no store law beyond totality is used.
-/
import Fl4Proofs.P1.Store
import Fl4Proofs.P0.Auto
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

/-- A bind that succeeds succeeds in its first computation. -/
theorem spec_bind_inv {α β : Type _} {m : Result α} {f : α → Result β} {P : β → Prop}
    (h : (Std.bind m f) ⦃ P ⦄) : ∃ x, m = ok x ∧ f x ⦃ P ⦄ := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

/-- The extraction's tuple binds continue with `uncurry`. -/
theorem uncurry_eta_fd {α β γ : Type _} (f : α → β → γ) (x : α × β) : uncurry f x = f x.1 x.2 := by
  obtain ⟨a, b⟩ := x; simp only [uncurry_apply_pair]

/-- `spec_bind_inv` as an elimination rule (goal-directed walks). -/
theorem spec_bind_imp {α β : Type _} {m : Result α} {f : α → Result β} {P : β → Prop} {G : Prop}
    (h : ∀ x, f x ⦃ P ⦄ → G) : (Std.bind m f) ⦃ P ⦄ → G := fun hb => by
  obtain ⟨x, -, hx⟩ := spec_bind_inv hb; exact h x hx

/-- `spec_bind_imp` for the typeclass bind. -/
theorem spec_bind_imp' {α β : Type _} {m : Result α} {f : α → Result β} {P : β → Prop} {G : Prop}
    (h : ∀ x, f x ⦃ P ⦄ → G) : (m >>= f) ⦃ P ⦄ → G := spec_bind_imp h

/-- Case split on an `if` under `spec` (goal-directed walks). -/
theorem spec_ite_imp {β : Type _} {c : Prop} [Decidable c] {x y : Result β} {P : β → Prop} {G : Prop}
    (h1 : c → x ⦃ P ⦄ → G) (h2 : ¬ c → y ⦃ P ⦄ → G) : (if c then x else y) ⦃ P ⦄ → G := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem spec_ex_fd {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) :
    ∃ v, m = ok v ∧ P v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem eq_of_spec_fd {α : Type _} {m : Result α} {y : α} (h : m ⦃ r => r = y ⦄) : m = ok y := by
  obtain ⟨v, hv, rfl⟩ := spec_ex_fd h; exact hv

theorem spec_of_eq_fd {α : Type _} {m : Result α} {y : α} (h : m = ok y) : m ⦃ r => r = y ⦄ := by
  rw [h]; exact (WP.spec_ok _).2 rfl

section
variable {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)

/-- **`fastpath.fault` declines without a trace.** -/
theorem fault_decline {s : S} {a : A} {t : obj.Tcb} {n : Std.U64} {s' : S} {a' : A}
    (h : fastpath.fault st ar s a t n = ok (false, s', a')) : s' = s ∧ a' = a := by
  have h' := spec_of_eq_fd h
  clear h
  unfold fastpath.fault at h'
  revert h'
  repeat' (first
    | (with_reducible_and_instances refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible_and_instances refine spec_bind_imp' (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible refine spec_ite_imp (fun _ => ?_) (fun _ => ?_))
    | split
    | (refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd]))
  all_goals intro h'
  all_goals rw [WP.spec_ok] at h'
  all_goals first
    | exact ⟨(congrArg (fun r => r.2.1) h').symm, (congrArg (fun r => r.2.2) h').symm⟩
    | simp at h'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`fastpath.reply_recv_found` declines without a trace.** -/
theorem reply_recv_found_decline {s : S} {a : A} {t : obj.Tcb} {rp ep : Std.U64} {s' : S} {a' : A}
    (h : fastpath.reply_recv_found st ar s a t rp ep = ok (false, s', a')) : s' = s ∧ a' = a := by
  have h' := spec_of_eq_fd h
  clear h
  unfold fastpath.reply_recv_found at h'
  revert h'
  repeat' (first
    | (with_reducible_and_instances refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible_and_instances refine spec_bind_imp' (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible refine spec_ite_imp (fun _ => ?_) (fun _ => ?_))
    | split
    | (refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd]))
  all_goals intro h'
  all_goals rw [WP.spec_ok] at h'
  all_goals first
    | exact ⟨(congrArg (fun r => r.2.1) h').symm, (congrArg (fun r => r.2.2) h').symm⟩
    | simp at h'

/-- **`fastpath.reply_recv` declines without a trace.** -/
theorem reply_recv_decline {s : S} {a : A} {s' : S} {a' : A}
    (h : fastpath.reply_recv st ar s a = ok (false, s', a')) : s' = s ∧ a' = a := by
  have h' := spec_of_eq_fd h
  clear h
  unfold fastpath.reply_recv at h'
  obtain ⟨t, -, h'⟩ := spec_bind_inv h'
  obtain ⟨o, -, h'⟩ := spec_bind_inv h'
  split at h'
  · rw [WP.spec_ok] at h'
    exact ⟨(congrArg (fun r => r.2.1) h').symm, (congrArg (fun r => r.2.2) h').symm⟩
  · rename_i p
    obtain ⟨rp, ep⟩ := p
    try simp only [uncurry_apply_pair] at h'
    exact reply_recv_found_decline st ar (eq_of_spec_fd h')

/-- `unknown_syscall_fault`: a run with the fast path enabled that ends
`false` is the run without it. -/
theorem usf_decline {s : S} {a : A} {n : Std.U64} {s' : S} {a' : A}
    (h : syscall.unknown_syscall_fault st ar s a n true = ok (false, s', a')) :
    syscall.unknown_syscall_fault st ar s a n false = ok (false, s', a') := by
  have h' := spec_of_eq_fd h
  clear h
  unfold syscall.unknown_syscall_fault at h' ⊢
  obtain ⟨⟨b, s1, a1⟩, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  try simp only [uncurry_apply_pair] at h'
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h' ⊢
    exact eq_of_spec_fd h'
  · simp only [↓reduceIte] at h' ⊢
    obtain ⟨t, e, h'⟩ := spec_bind_inv h'
    rw [e]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, Bool.false_eq_true]
    try simp only [↓reduceIte] at h'
    obtain ⟨⟨b1, s2, a2⟩, e2, h'⟩ := spec_bind_inv h'
    try simp only [uncurry_apply_pair] at h'
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte] at h'
      obtain ⟨e3, e4⟩ := fault_decline st ar e2
      rw [e3, e4] at h'
      exact eq_of_spec_fd h'
    · simp only [↓reduceIte, WP.spec_ok] at h'
      simp at h'

/-- `handle_unknown_syscall`: as `usf_decline`. -/
theorem hus_decline {s : S} {a : A} {n : Std.I64} {s' : S} {a' : A}
    (h : syscall.handle_unknown_syscall st ar s a n true = ok (false, s', a')) :
    syscall.handle_unknown_syscall st ar s a n false = ok (false, s', a') := by
  have h' := spec_of_eq_fd h
  clear h
  unfold syscall.handle_unknown_syscall at h' ⊢
  simp only [fl4_abi.config.PRINTING, fl4_abi.config.DEBUG_BUILD, fl4_abi.config.SET_TLS_BASE_SELF,
    ↓reduceIte, lift, bind_ok] at h' ⊢
  obtain ⟨t, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  by_cases h1 : n = fl4_abi.syscall.SysDebugPutChar
  · simp only [if_pos h1] at h' ⊢; exact eq_of_spec_fd h'
  simp only [if_neg h1] at h' ⊢
  by_cases h2 : n = fl4_abi.syscall.SysDebugDumpScheduler
  · simp only [if_pos h2] at h' ⊢; exact eq_of_spec_fd h'
  simp only [if_neg h2] at h' ⊢
  obtain ⟨⟨b, s1, a1⟩, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  try simp only [uncurry_apply_pair] at h'
  cases b
  swap
  · simp only [↓reduceIte] at h' ⊢; exact eq_of_spec_fd h'
  simp only [Bool.false_eq_true, ↓reduceIte] at h' ⊢
  by_cases h3 : n = fl4_abi.syscall.SysSetTLSBase
  · simp only [if_pos h3] at h' ⊢; exact eq_of_spec_fd h'
  simp only [if_neg h3] at h' ⊢
  by_cases h4 : n = fl4_abi.syscall.SysVMEnter
  swap
  · simp only [if_neg h4] at h' ⊢; exact usf_decline st ar (eq_of_spec_fd h')
  simp only [if_pos h4] at h' ⊢
  obtain ⟨i, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  by_cases h5 : (i != 0#u64) = true
  swap
  · simp only [if_neg h5] at h' ⊢; exact usf_decline st ar (eq_of_spec_fd h')
  simp only [if_pos h5] at h' ⊢
  obtain ⟨i1, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  by_cases h6 : (i1 != 0#u64) = true
  swap
  · simp only [if_neg h6] at h' ⊢; exact usf_decline st ar (eq_of_spec_fd h')
  simp only [if_pos h6] at h' ⊢
  exact eq_of_spec_fd h'

/-- **The entry with its fast paths enabled, where none answered, is the
general entry.** -/
theorem syscall_decline {s : S} {a : A} {n : Std.I64} {s' : S} {a' : A}
    (h : syscall.syscall st ar s a n true = ok (false, s', a')) :
    syscall.syscall st ar s a n false = ok (false, s', a') := by
  have h' := spec_of_eq_fd h
  clear h
  unfold syscall.syscall at h' ⊢
  simp only [lift, bind_ok] at h' ⊢
  obtain ⟨t, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  obtain ⟨nx, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  obtain ⟨s1, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  obtain ⟨i1, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  by_cases c1 : (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · simp only [if_pos c1] at h' ⊢
    exact usf_decline st ar (eq_of_spec_fd h')
  simp only [if_neg c1] at h' ⊢
  by_cases c2 : n < fl4_abi.syscall.SYSCALL_MIN
  · simp only [if_pos c2] at h' ⊢; exact hus_decline st ar (eq_of_spec_fd h')
  simp only [if_neg c2] at h' ⊢
  by_cases c3 : n > fl4_abi.syscall.SYSCALL_MAX
  · simp only [if_pos c3] at h' ⊢; exact hus_decline st ar (eq_of_spec_fd h')
  simp only [if_neg c3] at h' ⊢
  obtain ⟨⟨b, s2, a1⟩, e, h'⟩ := spec_bind_inv h'
  rw [e]; simp only [bind_ok, uncurry_apply_pair]
  try simp only [uncurry_apply_pair] at h'
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h' ⊢; exact eq_of_spec_fd h'
  simp only [↓reduceIte, Bool.false_eq_true] at h' ⊢
  by_cases c4 : n = fl4_abi.syscall.SysReplyRecv
  · simp only [if_pos c4] at h'
    obtain ⟨⟨b1, s3, a2⟩, e2, h'⟩ := spec_bind_inv h'
    try simp only [uncurry_apply_pair] at h'
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte] at h'
      obtain ⟨e3, e4⟩ := reply_recv_decline st ar e2
      rw [e3, e4] at h'
      exact eq_of_spec_fd h'
    · simp only [↓reduceIte, WP.spec_ok] at h'
      simp at h'
  · simp only [if_neg c4] at h'; exact eq_of_spec_fd h'

/-- **[P] The fast paths keep what the general path guarantees, where they
answer** (`FastAgree` narrowed to the runs of `handle_syscall_fast` that
end `true`, i.e. where `fastpath.fault` or `fastpath.reply_recv` took the
entry; a declined fast path is the general path, `syscall_decline`). l4v
counterpart: `Fastpath_C`'s `fastpath_call` / `fastpath_reply_recv` refine
the slow path on the path where they do not fall back to `slowpath`. -/
def FastAcc (s : S) (a : A) (n : Std.I64) (P : S × A → Prop) : Prop :=
  syscall.handle_syscall_general st ar s a n ⦃ P ⦄ →
    ∀ s' a', syscall.handle_syscall_fast st ar s a n = ok (true, s', a') → P (s', a')

/-- **`FastAcc` gives `FastAgree`** (total store and Arch, P0). -/
theorem FastAgree.of_acc (hS : P0.StoreTotal st) (hA : P0.ArchTotal ar) {s : S} {a : A} {n : Std.I64}
    {P : S × A → Prop} (hF : FastAcc st ar s a n P) : FastAgree st ar s a n P := by
  intro hg
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := spec_ex_fd (P0.syscall.handle_syscall_fast.p0 st ar s a n hS hA)
  have e' : syscall.syscall st ar s a n true = ok (b, s', a') := by
    unfold syscall.handle_syscall_fast at e; exact e
  have hs : syscall.handle_syscall st ar s a n = ok (s', a') := by
    unfold syscall.handle_syscall; rw [e']; simp only [bind_ok, uncurry_apply_pair]
  rw [hs, WP.spec_ok]
  cases b
  · have hgen : syscall.handle_syscall_general st ar s a n = ok (s', a') := by
      unfold syscall.handle_syscall_general; rw [syscall_decline st ar e']; simp only [bind_ok, uncurry_apply_pair]
    rw [hgen, WP.spec_ok] at hg; exact hg
  · exact hF hg s' a' e


/-! ## The postcondition-free form (m57 handoff)

`FastAcc` is per postcondition. The fast paths make the general path's
writes in another order, so the two end states agree in memory (and in the
Arch value: the same calls in the same order), not as terms of `S`.
`FastSame` is that agreement — the kernel theorem fastpath.rs states, free
of `P` — and `MemResp P` says that `P` reads the state through memory only;
together they give `FastAcc` (`FastAcc.of_same`). -/

/-- Two results agree in every aligned memory word, kernel-state base, CPU
and Arch (m58: aligned words only — `LawfulStore` pins `mem` after a write
only at aligned addresses, `mem_wr`, so two write orders can be shown to
agree only there). -/
def MemAg [L : LawfulStore st] (r r' : S × A) : Prop :=
  (∀ x, Aligned x → L.mem r.1 x = L.mem r'.1 x) ∧ L.ksb r.1 = L.ksb r'.1 ∧ L.cpu r.1 = L.cpu r'.1 ∧ r.2 = r'.2

/-- **[P] The fast paths' effect, free of a postcondition**: a run of
`handle_syscall_fast` that a fast path answered ends in memory where the
general path ends. -/
def FastSame [LawfulStore st] (s : S) (a : A) (n : Std.I64) : Prop :=
  ∀ s' a', syscall.handle_syscall_fast st ar s a n = ok (true, s', a') →
    ∃ r, syscall.handle_syscall_general st ar s a n = ok r ∧ MemAg st (s', a') r

/-- `P` reads the state through memory only. -/
def MemResp [LawfulStore st] (P : S × A → Prop) : Prop :=
  ∀ r r', MemAg st (A := A) r r' → P r' → P r

/-- **[P] The store is its memory** (m58): two states with the same aligned
words, kernel-state base and CPU are the same state. The platform's store is
physical memory read and written by aligned words (the kernel's only
accesses, `LawfulStore.mem_wr`), with `frame_masks` constant (`PlainStore`)
or itself in memory; an unaligned read is a function of the aligned words
around it. Without it `MemResp` is not derivable for the P1 / P3 posts:
`LawfulStore` leaves `mem (wr s a v) b` open at unaligned `b` and
`frame_masks` open, and `EntryInvs` / `RJ` mention store operations at the
state (`BlkOK st … s`, `RPlaced st … s`, `XTopAt … s`), so two states equal
in their aligned words need not satisfy the same such propositions.
l4v: the `machine_state`/`kheap` of `Fastpath_C` are total maps compared by
equality (`fastpath_corres` ends in `ccorres` on equal states). -/
def StoreExt [L : LawfulStore st] : Prop :=
  ∀ s s' : S, (∀ x, Aligned x → L.mem s x = L.mem s' x) → L.ksb s = L.ksb s' → L.cpu s = L.cpu s' → s = s'

/-- With `StoreExt` agreeing results are equal. -/
theorem MemAg.eq [L : LawfulStore st] (hX : StoreExt st) {r r' : S × A} (h : MemAg st r r') : r = r' := by
  obtain ⟨hm, hk, hc, ha⟩ := h
  obtain ⟨s, a⟩ := r; obtain ⟨s', a'⟩ := r'
  simp only at hm hk hc ha
  rw [hX s s' hm hk hc, ha]

/-- **Every postcondition reads the state through memory only** under
`StoreExt` (in particular P3's `KPost` and P1's
`∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs …`). -/
theorem MemResp.of_ext [LawfulStore st] (hX : StoreExt st) (P : S × A → Prop) : MemResp st P := by
  intro r r' h hp
  rw [MemAg.eq st hX h]; exact hp

theorem FastAcc.of_same [LawfulStore st] {s : S} {a : A} {n : Std.I64} {P : S × A → Prop}
    (h : FastSame st ar s a n) (hP : MemResp st P) : FastAcc st ar s a n P := by
  intro hg s' a' e
  obtain ⟨r, er, hm⟩ := h s' a' e
  rw [er, WP.spec_ok] at hg
  exact hP _ _ hm hg

/-- `FastSame` and `StoreExt` give `FastAcc` for every postcondition. -/
theorem FastAcc.of_ext [LawfulStore st] {s : S} {a : A} {n : Std.I64} {P : S × A → Prop}
    (hX : StoreExt st) (h : FastSame st ar s a n) : FastAcc st ar s a n P :=
  FastAcc.of_same st ar h (MemResp.of_ext st hX P)

end
end Fl4Proofs.P1
