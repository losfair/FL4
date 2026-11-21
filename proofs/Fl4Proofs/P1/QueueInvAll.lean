/-
P1: EntryHyps' `inv` assembled: `handle_invocation` (cap lookup, decode,
reply, restart to running) over every cap family.  The endpoint and
notification invocations are `ep_send.blk` and `ntfn_signal.blkF`; the null
and zombie caps are rejected.  Every other family's decode is named as a
hypothesis of one shape, `DecGap` (`InvGaps`).
-/
import Fl4Proofs.P1.QueueXfer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U X : Set U64}
variable {Q : U64 → U64 → List U64} {R : U64 → List U64} {P3Ok : S → Prop}

/-! ## The replies of `handle_invocation` -/

theorem msg.reply_success_empty.xs {s0 s : S} {t : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (ht : t ∈ T) :
    msg.reply_success_empty st s t ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  unfold msg.reply_success_empty
  refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) h ht (by simp [layout.reg.BADGE, layout.reg.RDI]))
    fun s1 h1 => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xs (v := w) h1 ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI])

set_option hygiene false in
local macro "smr" : tactic => `(tactic| (
  refine WP.spec_bind (msg.set_mr.xs hcur ht hb (by simp)) ?_
  rintro ⟨_, s'⟩ ⟨hcur, -⟩
  try simp only at hcur
  try simp only [WP.uncurry'_pair]))

theorem syscall.error_mrs.xs {s0 s : S} {t buf : U64} {e : error.SysError}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (ht : t ∈ T) (hb : BufOK U buf) :
    syscall.error_mrs st s t buf e ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ⦄ := by
  have hcur := h
  unfold syscall.error_mrs
  split
  · exact set_mr_last h ht hb (by simp)
  · exact set_mr_last h ht hb (by simp)
  · exact (WP.spec_ok _).2 h
  · smr
    exact set_mr_last hcur ht hb (by simp)
  · exact (WP.spec_ok _).2 h
  · split
    · smr
      exact faults.set_mrs_lookup_failure.xs hcur ht hb (by simp)
    · smr
      exact faults.set_mrs_lookup_failure.xs hcur ht hb (by simp)
  · exact (WP.spec_ok _).2 h
  · exact (WP.spec_ok _).2 h
  · exact (WP.spec_ok _).2 h
  · exact set_mr_last h ht hb (by simp)

/-- **An endpoint send's guard from `XG` at its start** (`ep_send.blk`'s:
the restart, then the receiver dequeued). -/
theorem XG.sendG {P3Ok : S → Prop} {Ac : Set U64} {s : S} {ct e : U64}
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : CanBlock st T Ac s ct) :
    ∀ s1 s2, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → H e = some .ep →
      (L.epState s1 e = 1#u64 ∨ L.epState s1 e = 2#u64) → endpoint.ep_dequeue st s1 e (L.epQ s1 e).head = ok s2 →
      XG st T Cs Ω H Sg Scs Z P3Ok s2 := by
  intro s1 s2 e1 hH hst e2
  obtain ⟨Q, R, h0⟩ := h.1
  have F1 := spec_at (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s ct _ h0 hc.mem) e1
  obtain ⟨⟨⟨Q1, R1, h1⟩, -⟩, -⟩ := spec_at (sched.set_thread_state.restart_blk (Es := ∅) s ct h hc.mem hc.nb hc.nrp) e1
  exact (hG.foot F1).foot (spec_at (endpoint.ep_dequeue.head_kw (Scs := Scs) h1 hH hst) e2)

theorem syscall.reply_error.xs (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s0 s : S} {t : U64}
    {e : error.SysError} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (ht : t ∈ T)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.reply_error st s t e ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold syscall.reply_error
  refine WP.spec_bind (E.buf _ _ _ _ s t hG h.1 ht) fun buf hb => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) h ht (by simp [layout.reg.BADGE, layout.reg.RDI]))
    fun s1 h1 => ?_
  refine WP.spec_bind (syscall.error_mrs.xs (e := e) h1 ht hb) ?_
  rintro ⟨len, s2⟩ h2
  simp only at h2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun r : S × U64 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.1) ?_ ?_
  · simp only [fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte]
    split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [syscall.DEBUG_MESSAGE_START]
      step as ⟨i, hi⟩
      refine WP.spec_bind (P0.msg.buf_get.p0 st s2 buf i hS) fun w _ => ?_
      try simp only [lift, bind_ok]
      refine WP.spec_bind (msg.buf_set.xs (v := w &&& ~~~255#u64) h2 hb h0 (by omega)) fun s4 h4 => ?_
      exact (WP.spec_ok _).2 h4
    · exact (WP.spec_ok _).2 h2
  rintro ⟨s3, len1⟩ h3
  simp only at h3
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.error.SysError.code.p0 e) fun i _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xs (v := w) h3 ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI])

/-- `XS` from `BXI` and back. -/
theorem BXI.xs {s : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) :
    ∃ Q R, XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s s := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  exact ⟨Q, R, XS.start ⟨h0, hB, hX, hS, hSg, hU⟩⟩

theorem XS.bxi {s0 s : S} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  ⟨⟨Q, R, h.1.1⟩, h.1.2.1, h.1.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.1⟩

/-- A restarted thread set running. -/
theorem sched.set_thread_state.running_bxi {s : S} {t : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hr : L.mem s (stA t) = sched.TS_RESTART) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t :=
    hX.noref (h0.tcbs t ht) (by rw [hr]; exact restart_ne.1) (by rw [hr]; exact restart_ne.2)
  refine WP.spec_mono (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_running running_ne
    (Or.inr (by rw [hr]; exact not_blocked_restart)) hnoref
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
  rintro s' ⟨h1, hB1, hX1, hS1, hSg1, -, -⟩
  exact ⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hSg1, hS1⟩

/-! ## The cap families and the decode gaps -/

/-- The families of caps `decode_invocation` dispatches on. -/
inductive CapFam where
  | null | untyped | endpoint | notification | reply | cnode | thread | irqControl | irqHandler | zombie
  | domain | schedContext | schedControl | vspace | vcpu | ept | ioPortControl | ioPort
  deriving DecidableEq

/-- The family of a cap (`vspace`: frames, the paging structures, the ASID
control and pool caps). -/
def capFam : capability.Cap → CapFam
  | .Null => .null
  | .Untyped .. => .untyped
  | .Endpoint .. => .endpoint
  | .Notification .. => .notification
  | .Reply .. => .reply
  | .CNode .. => .cnode
  | .Thread .. => .thread
  | .IrqControl => .irqControl
  | .IrqHandler .. => .irqHandler
  | .Zombie .. => .zombie
  | .Domain => .domain
  | .SchedContext .. => .schedContext
  | .SchedControl .. => .schedControl
  | .Frame .. => .vspace
  | .PageTable .. => .vspace
  | .PageDirectory .. => .vspace
  | .Pdpt .. => .vspace
  | .Pml4 .. => .vspace
  | .Vcpu .. => .vcpu
  | .Ept .. => .ept
  | .AsidControl => .vspace
  | .AsidPool .. => .vspace
  | .IoPortControl => .ioPortControl
  | .IoPort .. => .ioPort

/-- What a decoded invocation leaves: the invariants (with a possibly
smaller active set) and, when it was preempted, the current thread's step
(`CurStep`) and what the preemption point needs. -/
def DecPost (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s : S) (r : core.result.Result Unit error.Exc) (s' : S) : Prop :=
  ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ∧
    (r = .Err .Preempted → CurStep st Ac Ac' s s' ∧ L.actionW s' ≠ L.curW s' ∧
      (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s'))))

/-- The typing of an invoked cap (P3's `valid_cap`): `CapTyped`, thread caps
name TCBs, and SC caps name non-null SC objects other than the idle
thread's. -/
def CapOK (st : machine.Store S) [L : LawfulStore st] (T Rp Scs Nt : Set U64) (H : Heap) (s : S)
    (c : capability.Cap) : Prop :=
  CapTyped H Rp Nt c ∧ (∀ p, c = .Thread p → p ∈ T) ∧
    (∀ p b, c = .SchedContext p b → p ∈ Scs ∧ p ≠ 0#u64 ∧ L.mem s (scTcbA p) ≠ L.idleW s)

/-- The words of the current core's node (where `remote_tcb_stall` writes). -/
def NodeW (st : machine.Store S) [L : LawfulStore st] (s : S) (b : U64) : Prop :=
  ∃ o : U64, o.val < 4288 ∧ o.val ≠ 88 ∧ b = L.nodeAt s (L.cpu s) o

/-- What `decode_invocation` may assume: the invariants, the current SC is
active, the invoked and the extra caps are typed (the extra caps also after writes
of the current core's node words), the current thread is
runnable, can block, and is to be resumed (seL4: invocations run with
`ResumeCurrentThread`), and the user words are outside the kernel objects. -/
structure DecPre (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U Ac : Set U64) (s : S) (cap : capability.Cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop where
  bxi : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  csc : L.cscW s ∈ Ac
  cap : CapOK st T Rp Scs Nt H s cap
  extra : ∀ s', WritesIn st s s' (NodeW st s) → ∀ sl ∈ extra.val, sl ≠ 0#u64 →
    obj.Slot.cap st sl s' ⦃ c => CapOK st T Rp Scs Nt H s' c ⦄
  run : Runnable (L.mem s (stA (L.curW s)))
  act : L.actionW s = 0#u64
  hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))
  cb : CanBlock st T Ac s (L.curW s)
  user : UserOK st T Cs Ω H U s

/-- **The gap shape**: `decode_invocation` on a cap of the family `f` keeps
the invariants (`DecPost`), from `DecPre`. -/
def DecGap (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) (f : CapFam) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (lbl len : U64) (slot : obj.Slot) (cap : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    capFam cap = f → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → CapSlotW T Ω Sg slot →
    EntAt st P3Ok s →
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄

/-- What a decoded invocation leaves when the heap may grow (a retype): the
invariants over some admissible set tuple, the current thread among its
threads. -/
def DecPostG (st : machine.Store S) [L : LawfulStore st] (Adm : PSets → Prop) (Cs : Set U64) (Ac : Set U64) (s : S)
    (r : core.result.Result Unit error.Exc) (s' : S) : Prop :=
  ∃ σ', Adm σ' ∧ L.curW s ∈ σ'.T ∧ DecPost st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Rp σ'.Scs σ'.Nt σ'.Z Ac s r s'

/-- A spec with the result's equation. -/
theorem spec_eqv {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : m ⦃ r => m = ok r ∧ P r ⦄ := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

/-- `DecGap` with the heap possibly growing (`DecPostG`); the invoked slot
holds the invoked cap. -/
def DecGapG (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (Adm : PSets → Prop)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop)
    (f : CapFam) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (lbl len : U64) (slot : obj.Slot) (cap : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    capFam cap = f → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → CapSlotW T Ω Sg slot →
    obj.Slot.cap st slot s = ok cap → EntAt st P3Ok s →
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPostG st Adm Cs Ac s r s' ⦄

/-- A fixed-heap gap is a growing-heap one (`σ' := σ`). -/
theorem DecGap.toG {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} {U : Set U64} {f : CapFam}
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) (g : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok f) :
    DecGapG st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok f :=
  fun Ac s a lbl len slot cap blk call don fp buf extra hf D hs _ he =>
    WP.spec_mono (g Ac s a lbl len slot cap blk call don fp buf extra hf D hs he) fun r hr => by
      obtain ⟨r1, s1, a1⟩ := r
      exact ⟨_, hσ, D.bxi.1.choose_spec.choose_spec.curT, hr⟩

/-- The families whose decode P1 does not prove, each a `DecGap` (untyped's
over a growing heap, `DecGapG`). -/
structure InvGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  untyped : DecGapG st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok .untyped
  reply : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .reply
  cnode : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode
  thread : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread
  irqControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqControl
  irqHandler : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqHandler
  domain : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .domain
  schedContext : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedContext
  schedControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedControl
  vspace : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vspace
  vcpu : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu
  ept : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ept
  ioPortControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPortControl
  ioPort : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPort

/-- The facts at an invocation (P3's): the current thread is runnable and to
be resumed, and the caps it invokes (the slot's and the extra caps) are
typed. -/
structure InvHyps (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop where
  cur : ∀ (Ac : Set U64) (s : S), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    Runnable (L.mem s (stA (L.curW s))) ∧ L.actionW s = 0#u64
  slotcap : ∀ (Ac : Set U64) (s : S) (cptr : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    cspace.lookup_slot st s (L.curW s) cptr ⦃ r => ∀ x, r = .Ok x →
      obj.Slot.cap st x.slot s ⦃ c => CapOK st T Rp Scs Nt H s c ⦄ ⦄
  /-- The looked-up slot of the invoked cap is a cap slot (its four words are cap-slot words). -/
  lookupSlot : ∀ (Ac : Set U64) (s : S) (cptr : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    cspace.lookup_slot st s (L.curW s) cptr ⦃ r => ∀ x, r = .Ok x → CapSlotW T Ω Sg x.slot ⦄
  extra : ∀ (Ac : Set U64) (s : S) (b : U64) (tag : msginfo.MessageInfo), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ipc.lookup_extra_caps st s (L.curW s) b tag ⦃ r => ∀ e, r = .Ok e →
      ∀ s', WritesIn st s s' (NodeW st s) → ∀ sl ∈ e.val, sl ≠ 0#u64 →
        obj.Slot.cap st sl s' ⦃ c => CapOK st T Rp Scs Nt H s' c ⦄ ⦄

/-- Any error result with the state unchanged. -/
theorem DecPre.err {U : Set U64} {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (r : core.result.Result Unit error.Exc) :
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s :=
  ⟨Ac, D.bxi, fun _ => ⟨⟨rfl, rfl, fun h1 h2 => absurd h1 h2, Or.inl rfl⟩,
    fun e => notT_small (v := L.curW s) D.bxi.1.choose_spec.choose_spec.tcbs
      (by have := D.act; rw [e] at this; rw [this]; decide) D.bxi.1.choose_spec.choose_spec.curT, D.hcsc⟩⟩

theorem DecPost.keep {s : S} {r : core.result.Result Unit error.Exc} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hr : r ≠ .Err .Preempted) : DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s :=
  ⟨Ac, h, fun e => absurd e hr⟩

/-- **`decode_invocation` over every cap family**: the endpoint and
notification sends (`ep_send.blk`, `ntfn_signal.blkF`), the rejected null and
zombie caps and receive-only caps, and the `InvGaps`. -/
theorem syscall.decode_invocation.dec0 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop}
    (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (G : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (s : S) (a : A) (lbl len : U64) (slot : obj.Slot) (cap : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hslot : CapSlotW T Ω Sg slot)
    (he : EntAt st P3Ok s) (hu : capFam cap ≠ .untyped) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have h := D.bxi
  have hct : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hrun := D.run
  have hsc : L.mem s (scA (L.curW s)) ≠ 0#u64 := h.2.1.resume D.act
  have hcb := D.cb
  have hU := D.user
  have hcap := D.cap.1
  have rej : ∀ (e : error.Exc), e ≠ .Preempted →
      (ok ((core.result.Result.Err e : core.result.Result Unit error.Exc), s, a) : Result _) ⦃ r s' _ =>
        DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := fun e he =>
    (WP.spec_ok _).2 (DecPost.keep h fun e' => he (by cases e'; rfl))
  cases cap with
  | Null =>
    unfold syscall.decode_invocation
    step with sched.cur_thread.spec as ⟨ct, _⟩
    exact DecPost.keep h (by simp)
  | Zombie =>
    unfold syscall.decode_invocation
    step with sched.cur_thread.spec as ⟨ct, _⟩
    exact DecPost.keep h (by simp)
  | Endpoint p b sd rc g gr =>
    unfold syscall.decode_invocation
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    try dsimp only
    split
    · refine WP.spec_mono (ep_send.blk hA (xferOK_of hA E) s a blk call b g gr don _ p
        (XG.sendG he.xg h.blk hcb) h.blk hU hcb
        (fun _ => hsc) (hcap.1 _ _ _ _ _ _ rfl)) ?_
      rintro ⟨r, s', a'⟩ hr
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨Ac, BlkOK.bxi hr.2, fun e => by rw [hr.1] at e; cases e⟩
    · exact rej (.Sys (.InvalidCapability 0#u64)) (by simp)
  | Notification p b sd rc =>
    unfold syscall.decode_invocation
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    try dsimp only
    split
    · obtain ⟨hn, hH⟩ := hcap.2.1 _ _ _ _ rfl
      refine WP.spec_mono (ntfn_signal.blkF hA s a _ p b h.blk hct hrun hn hH) ?_
      rintro ⟨r, s', a'⟩ hr
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨Ac, BlkOK.bxi hr.2.1, fun e => by rw [hr.1] at e; cases e⟩
    · exact rej (.Sys (.InvalidCapability 0#u64)) (by simp)
  | Untyped => exact absurd rfl hu
  | Reply => exact G.reply _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | CNode => exact G.cnode _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | Thread => exact G.thread _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | IrqControl => exact G.irqControl _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | IrqHandler => exact G.irqHandler _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | Domain => exact G.domain _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | SchedContext => exact G.schedContext _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | SchedControl => exact G.schedControl _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | Frame => exact G.vspace _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | PageTable => exact G.vspace _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | PageDirectory => exact G.vspace _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | Pdpt => exact G.vspace _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | Pml4 => exact G.vspace _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | AsidControl => exact G.vspace _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | AsidPool => exact G.vspace _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | Vcpu => exact G.vcpu _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | Ept => exact G.ept _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | IoPortControl => exact G.ioPortControl _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he
  | IoPort => exact G.ioPort _ _ _ _ _ _ _ _ _ _ _ _ _ rfl D hslot he

/-- **`decode_invocation` over every cap family**, the heap possibly growing
(an untyped's retype, `InvGaps.untyped`; the others keep the set tuple). -/
theorem syscall.decode_invocation.dec {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop}
    (hA : P0.ArchTotal ar) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (G : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (s : S) (a : A) (lbl len : U64) (slot : obj.Slot) (cap : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hslot : CapSlotW T Ω Sg slot)
    (hcs : obj.Slot.cap st slot s = ok cap) (he : EntAt st P3Ok s) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPostG st Adm Cs Ac s r s' ⦄ := by
  by_cases hu : capFam cap = .untyped
  · exact G.untyped _ _ _ _ _ _ _ _ _ _ _ _ _ hu D hslot hcs he
  · exact WP.spec_mono (syscall.decode_invocation.dec0 hA E G s a lbl len slot cap blk call don fp buf extra D
      hslot he hu) fun r hr => by
        obtain ⟨r1, s1, a1⟩ := r
        exact ⟨_, hσ, D.bxi.1.choose_spec.choose_spec.curT, hr⟩

/-- (P3, from its post-decode relation) A decode that ends in a syscall
error leaves an `XG` state (the error reply writes the IPC buffer). -/
def DecErrG (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Scs : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ (s0 : S) (a0 : A) (lbl len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (e : error.SysError) (s1 : S) (a1 : A), EntAt st P3Ok s0 →
    syscall.decode_invocation st ar s0 a0 lbl len slot cap blk call don fp buf extra =
      ok (.Err (.Sys e), s1, a1) → XG st T Cs Ω H Sg Scs Z P3Ok s1

/-- **EntryHyps' `inv`: `handle_invocation` over every cap family**, from
the decode gaps `InvGaps`, the invocation facts `InvHyps`, the transfer's
placement facts `XferHyps`, `recvOK`'s and the faults of the current
thread. -/
theorem syscall.handle_invocation.inv {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop}
    (hA : P0.ArchTotal ar) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (G : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (I : InvHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (recvOK : ∀ σ' : PSets, Adm σ' → ∀ (Ac : Set U64) (s : S), BXIs st Cs σ' Ac s →
      CanBlock st σ'.T Ac s (L.curW s) ∧ UserOK st σ'.T Cs σ'.Ω σ'.H U s)
    (XF : ∀ σ' : PSets, Adm σ' → XferHyps st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Rp σ'.Scs σ'.Nt σ'.Z U P3Ok)
    (EG : ∀ σ' : PSets, Adm σ' → DecErrG st ar σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Scs σ'.Z P3Ok)
    (hflt : ∀ (Ac : Set U64) (s : S) (a : A) (f : error.Fault), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      EntAt st P3Ok s →
      faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄)
    (s : S) (a : A) (call blk don fp : Bool) (cptr : U64) (he : EntAt st P3Ok s)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcA : L.cscW s ∈ Ac)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) :
    syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s' _ => ∃ σ', Adm σ' ∧ ∃ Ac',
      BXIs st Cs σ' Ac' s' ∧
      (∀ e, r = .Err e → CurStep st Ac Ac' s s' ∧ L.actionW s' ≠ L.curW s' ∧
        (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  -- the fault paths
  have F : ∀ f, (do
      let (s1, a1) ← faults.handle_fault st ar s a (L.curW s) f
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)) ⦃ r s' _ => ∃ σ', Adm σ' ∧ ∃ Ac',
        BXIs st Cs σ' Ac' s' ∧
        (∀ e, r = .Err e → CurStep st Ac Ac' s s' ∧ L.actionW s' ≠ L.curW s' ∧
          (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ⦄ := fun f => by
    refine WP.spec_bind (hflt Ac s a f h he) ?_
    rintro ⟨s1, a1⟩ ⟨Ac1, h1⟩
    try simp only [WP.uncurry'_pair]
    exact (WP.spec_ok _).2 ⟨_, hσ, Ac1, h1, fun e he => by cases he⟩
  have K : (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a) : Result _) ⦃ r s' _ => ∃ σ', Adm σ' ∧ ∃ Ac',
        BXIs st Cs σ' Ac' s' ∧
        (∀ e, r = .Err e → CurStep st Ac Ac' s s' ∧ L.actionW s' ≠ L.curW s' ∧
          (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ⦄ :=
    (WP.spec_ok _).2 ⟨_, hσ, Ac, h, fun e he => by cases he⟩
  unfold syscall.handle_invocation
  step with sched.cur_thread.spec as ⟨t, et⟩
  have e : t = L.curW s := et
  subst e
  refine WP.spec_bind (P0.msg.msg_info.p0 st s _ hS) fun info _ => ?_
  refine WP.spec_bind (WP.spec_and (I.slotcap Ac s cptr he h) (I.lookupSlot Ac s cptr he h)) fun r ⟨hr, hsl⟩ => ?_
  rcases r with r1 | lf
  · try simp only
    refine WP.spec_bind (spec_eqv (hr r1 rfl)) fun cap ⟨ecap, hcap⟩ => ?_
    refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s false _ hS) fun buf _ => ?_
    refine WP.spec_bind (I.extra Ac s buf info he h) fun r2 hx => ?_
    rcases r2 with ex | f
    · try simp only
      refine WP.spec_bind (Pₘ := fun _ => True) (by
        split
        · split <;> exact (WP.spec_ok _).2 trivial
        · exact (WP.spec_ok _).2 trivial) fun length _ => ?_
      obtain ⟨hrun, hact⟩ := I.cur Ac s he h
      obtain ⟨hcb, hU⟩ := recvOK _ hσ Ac s h
      refine WP.spec_bind (spec_eq' (syscall.decode_invocation.dec hA hσ E G s a info.label length r1.slot cap
        blk call don fp buf ex ⟨h, hcA, hcap, hx ex rfl, hrun, hact, hcsc, hcb, hU⟩ (hsl r1 rfl) ecap he)) ?_
      rintro ⟨r3, s1, a1⟩ ⟨eqD, σ1, hσ1, hct1, Ac1, h1, hp⟩
      try simp only [WP.uncurry'_pair]
      obtain ⟨-, hU1⟩ := recvOK σ1 hσ1 Ac1 s1 h1
      obtain ⟨Q1, R1, x1⟩ := BXI.xs h1 hU1
      rcases r3 with _ | e1
      · try simp only
        step with obj.Tcb.state.spec as ⟨v, ev⟩
        split
        · rename_i hv
          refine WP.spec_bind (Pₘ := fun s2 => XS st σ1.T Cs σ1.Ω σ1.H σ1.Sg σ1.Rp σ1.Scs σ1.Nt σ1.Z U Ac1 ∅ Q1 R1 s1 s2) ?_ ?_
          · split
            · exact msg.reply_success_empty.xs x1 hct1
            · exact (WP.spec_ok _).2 x1
          intro s2 x2
          have hst : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART := by
            rw [stA_eq, x2.fr.2.2.2.2.1 _ hct1 _ (by simp) (by simp) (by simp), ← stA_eq, ← ev, hv]
          refine WP.spec_bind (sched.set_thread_state.running_bxi x2.bxi hct1 hst) fun s3 h3 => ?_
          exact (WP.spec_ok _).2 ⟨σ1, hσ1, Ac1, h3, fun e he => by cases he⟩
        · exact (WP.spec_ok _).2 ⟨σ1, hσ1, Ac1, h1, fun e he => by cases he⟩
      · cases e1 with
        | Fault _ => exact (WP.spec_ok _).2 ⟨σ1, hσ1, Ac1, h1, fun e he => by cases he⟩
        | Lookup _ => exact (WP.spec_ok _).2 ⟨σ1, hσ1, Ac1, h1, fun e he => by cases he⟩
        | Sys e2 =>
          try simp only
          split
          · refine WP.spec_bind (syscall.reply_error.xs (e := e2) (XF σ1 hσ1) x1 hct1
            (EG σ1 hσ1 s a _ _ _ _ _ _ _ _ _ _ e2 s1 a1 he eqD)) fun s2 x2 => ?_
            exact (WP.spec_ok _).2 ⟨σ1, hσ1, Ac1, x2.bxi, fun e he => by cases he⟩
          · exact (WP.spec_ok _).2 ⟨σ1, hσ1, Ac1, h1, fun e he => by cases he⟩
        | Preempted =>
          exact (WP.spec_ok _).2 ⟨σ1, hσ1, Ac1, h1, fun e he => hp rfl⟩
    · try simp only
      split
      · exact F f
      · exact K
  · try simp only
    split
    · exact F _
    · exact K

/-! ## The kernel entry from the gaps and the placement facts -/

/-- The P3 placement facts the kernel entry rests on (with `InvGaps`):
the transfer's (`XferHyps`), the invocation's (`InvHyps`), `tmoOK`,
`blkU`, `recvOK` and `irqcap` (as in `EntryHyps`), `dbg`: the thread caps the
debug syscalls invoke name TCBs, and `tmoAny`. -/
structure P3Place (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  xfer : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  inv : InvHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok
  tmoOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s ∧
    ∀ i, (i = layout.tcb.SLOT_TIMEOUT_HANDLER ∨ i = layout.tcb.SLOT_FAULT_HANDLER) →
      obj.Tcb.slot (L.curW s) i ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄
  blkU : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s
  recvOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    (∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄) ∧
    (∀ n ∈ Nt, L.epState s n ≠ 3#u64)
  irqcap : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ∀ i : U64, i.val < 128 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2, c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄
  dbg : ∀ (Ac : Set U64) (s : S), EntAt st P3Ok s → EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    syscall.invoked_cap st s (L.curW s) ⦃ c => ∀ x, c = .Thread x → x ∈ T ⦄
  /-- (P3) A decode ending in a syscall error leaves an `XG` state. -/
  errG : DecErrG st ar T Cs Ω H Sg Scs Z P3Ok
  /-- (P3, from its post-invocation relation; `EntryHyps0.postG`) The states
  after an invocation and its preemption point are `XG` states. -/
  postG : ∀ (s0 : S) (a0 : A) (call blk don fp : Bool) (cptr : U64) (r : core.result.Result Unit error.Exc)
    (s1 : S) (a1 : A), EntAt st P3Ok s0 → syscall.handle_invocation st ar s0 a0 call blk don fp cptr = ok (r, s1, a1) →
    XG st T Cs Ω H Sg Scs Z P3Ok s1 ∧ ∀ (b : Bool) (s2 : S) (a2 : A),
      syscall.after_invocation st ar s1 a1 r = ok (b, s2, a2) → XG st T Cs Ω H Sg Scs Z P3Ok s2
  /-- The timeout-handler cap of any thread is typed (`tmoOK`'s, for a thread
  other than the current one: the reply's caller's timeout fault). -/
  tmoAny : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
    obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄

/-- **`EntryHyps` from the decode gaps and the placement facts** (those of
every admissible tuple, `PF`, for after a retype). -/
theorem EntryHyps.of_gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    (PF : ∀ σ' : PSets, Adm σ' → P3Place st ar σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Rp σ'.Scs σ'.Nt σ'.Z U P3Ok)
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (G : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    EntryHyps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
  have hxf := xferOK_of hA P.xfer
  have hflt : ∀ (Ac : Set U64) (s : S) (a : A) (f : error.Fault), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      EntAt st P3Ok s →
      faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ :=
    fun Ac s a f h he => by
      obtain ⟨hc, hU, hcap⟩ := P.tmoOK Ac s he.xg h
      exact WP.spec_mono (faults.handle_fault.bxi hA hxf s a _ f (XG.faultG he.xg h.blk hU hc) h.blk hU hc
        (hcap _ (Or.inr rfl)))
        fun r hr => by obtain ⟨s', a'⟩ := r; exact ⟨Ac, BlkOK.bxi (by simpa using hr)⟩
  exact EntryHyps.of hA hxf P.tmoOK
    (fun Ac s a call blk don fp cptr he h hcA _ hcsc => syscall.handle_invocation.inv hA hσ P.xfer G P.inv
      (fun σ' h' Ac s h => (PF σ' h').blkU Ac s h)
      (fun σ' h' => (PF σ' h').xfer) (fun σ' h' => (PF σ' h').errG) hflt s a call blk don fp cptr he h hcA hcsc)
    P.blkU P.recvOK P.irqcap (fun Ac s a n he h => syscall.debug_syscall.entry hA s a n h (P.dbg Ac s he h)) P.postG

/-- **Native kernel entries keep `EntryInv`, from the decode gaps `InvGaps`
and the P3 placement facts `P3Place`** of every admissible tuple; the entry
ends over some admissible tuple. -/
theorem kernel_entry.entry_of {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXG st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_old st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry hA TX (fun σ h' => ⟨EntryHyps.of_gaps hA h' (fun σ'' h'' => (GF σ'' h'').1) (GF σ h').1
    (GF σ h').2.1, (GF σ h').2.2⟩) hσ s a hP h

end

end Fl4Proofs.P1
