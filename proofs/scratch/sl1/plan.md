## sl1 (branch par/sl1 in FL4-sc, on 03327de9 = int/j2 incl. sb2, vi1) — ScLive carried: typed form, frame family, binding writers (NOT finished)
Goal (sb2 handoff): carry `ScLive` across the entry (`kentry_scLive` / `kcall_scLive`) in sb2's typed form, then tops
carrying `ScInv ∧ ScLive`. Spec-only, namespace `Fl4Proofs.P3.SInvL`, modules SpecInvSl*.lean (root imports them).
- **The carried form (SpecInvSlK)**: `liveO o` = the binding part of l4v `live`: a TCB with `tcbSchedContext ≠ none`,
  an SC with `scTcb ≠ none ∨ scNtfn ≠ none ∨ scReplies ≠ []` (`scLv`; the SC's notification and reply stack are
  counted because `maybe_donate_sc` donates a notification's SC and `reply_remove` the SC of a reply stack, either
  possibly bound to no TCB — with `scTcb` alone those donations would make a cap-less SC bound). `NCap p c` (thread cap
  or SC cap to `p`), `HasN σ p`, `Nm I σ p := HasN σ p ∨ p = I.1 ∨ p = I.2`, **`ScLiveT I σ := ∀ p o, kheap p = some o
  → liveO o → p ≠ I.1 → p ≠ I.2 → HasN σ p`** (`I` = (idle thread, idle SC), FIXED parameters so the family reads the
  heap only), **`SL I K σ := ScLiveT I σ ∧ ∀ p ∈ K, Nm I σ p`** (il1's IL pattern; `K`: objects read live or named by
  a decoded cap; `sl_consL` adds a live object read at the state). Typed caps make every removal of another cap kind
  (and every Zombie) free.
- Leaves (SpecInvSlK): `sl_update` / `SLOK` (caps kept, a new live object only at a live one or at `K`),
  `sl_setObject_p`, setObject / set_simple_ko / thread_set (`(f x).tcbSchedContext ≠ none → x.tcbSchedContext ≠ none`,
  so unbinding is a leaf) / arch_thread_set / as_user / set_mrs / update_sched_context (`scLv (f y) → scLv y`:
  unbinding and reply-stack shrinking are leaves: `scLv_keep`, `scLv_replies`) / set_thread_state /
  option_update_thread, machine / extended ops; `setCap_live` (set_cap writes no live object), **`sl_setCap_p`** with
  `NSafe` (old cap no thread/SC cap, or names what the new one names, or another slot names its object, or its object
  is not live / idle and not in `K`), `sl_setCap_nt`, `sl_capInsert`, `sl_emptySlot_p`; `sl_auto` / `sl_leaf`.
- **Generated family SpecInvSlF1..F6** (339 lemmas `SLK Iq Kq f`, scratch/sl1/mksl.sh = il1's gen.py/closure.py, hard.txt
  = il1's cap-removing / decode-dependent seeds + the binding writers schedContextDonate / schedContextBindTcb /
  schedContextBindNtfn / bindScReply, extra.txt = fl4Awaken (its manual text calls sendSignal); caller closure in
  closure.log). Covers every unbinding writer (sched_context_unbind_*, unbind_from_sc, maybe_return_sc, suspend,
  cancel_all_ipc / signals, cancel_badged_sends, restart, reply_unlink_*, reply_remove_tcb), the budget/refill writers,
  decodes, lookups, IPC transfer, retype-free arch code.
- SpecInvSlW (binding writers): `sl_threadSetK` / `sl_updateSchedContextK` (any write at an object of `K`),
  **`sl_schedContextDonate c t (c ∈ K) (t ∈ K)`**, `sl_schedContextBindTcb`, `sl_schedContextBindNtfn (c ∈ K)`,
  `sl_bindScReply (c ∈ K)`, **`sl_replyPush (callee ∈ K) : HK (SL I K ∧ ScBackS) (SL I K)`** (the caller's SC, read bound
  to the caller, is bound back by sb1's ScBackS, hence live: `K := a.toList ++ K`), **`sl_replyRemove (caller ∈ K)`** (the
  SC holding the reply, `sc_with_reply`, has a non-empty stack: live, joins `K` at the read).
- SpecInvSlI1..I6: **no spec function writes `idleSc`** (`IdleScIs`, family `IsK`; sg1's SpecInvSgI1..I6 renamed:
  `isk_fl4KernelEntrySyscall`, `isk_fl4CallKernel`).
- SpecInvSlT: `IdleScOutV σ := IrqOutV (fun _ => σ.idleSc) (uV σ)` [carried with SL; l4v `valid_global_refs`,
  `idle_sc_ptr ∈ global_refs`] — kept by sg1's `S N M` family for M = fun _ => σ.idleSc (sgN_kentry / sgN_fl4CallKernel
  keep `IrqOutV M` for ANY fixed M) with `isk_*` for the pointer; **`scLive_of : ScLiveT (idleP σ) σ → IdleOutV σ →
  IdleScOutV σ → ScLive σ`**, `boot_scLiveT`, `boot_idleScOutV`.
