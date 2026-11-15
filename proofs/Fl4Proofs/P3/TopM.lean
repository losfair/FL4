/-
P3 (DESIGN.md §9): **the top-level posts with the MDB invariants**
(`MdbOKV`: `MdbOK`, i.e. VSpace's frame invariant, `UtInv` and `NoOverlap`
(MdbStepInv), with `UtWin` and `Vs.VsMdbInv` (MdbStepVs)),
parallel to TopF / HandleTop's (which carry the frame invariant only):
`TopPostM` / `DecOKM`, `TopPostDM` / `DecOKDM`, `decode_invocation_refinesDM`,
`RelTopM`, `TopPostRM` / `DecOKRM`, and `handle_invocation_refinesM`.
`DecOKM.toF` / `TopPostDM.toF` forget the invariants beyond the frame
invariant.
-/
import Fl4Proofs.P3.HandleTop
import Fl4Proofs.P3.MdbStepVs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`TopPost` with the frame invariant** after the invocation. -/
def TopPostM (σ : Fl4Spec.State Unit) (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, ∃ th' G',
      ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      MdbOKV (L.ksb s) (L.mem res.2.1) G')

theorem TopPostM.toF {σ : Fl4Spec.State Unit} {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation}
    {s : S} {res : core.result.Result Unit error.Exc × S × A} (h : TopPostM (L := L) σ blk call don m s res) :
    TopPostF (L := L) σ blk call don m s res := by
  rcases h with h | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7⟩
  · exact Or.inl h
  · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7.1.1⟩

/-- The statement for one cap, with the frame invariant. -/
abbrev DecOKM (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostM (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ⦄

theorem DecOKM.toF {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    (h : DecOKM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKF (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer :=
  WP.spec_mono h (fun _ h => h.toF)

/-- **`TopPostM` with the domain schedule.** -/
def TopPostDM (σ : Fl4Spec.State Unit) (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, ∃ th' G',
      ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2 ∧ MdbOKV (L.ksb res.2.1) (L.mem res.2.1) G')

theorem TopPostDM.toF {σ : Fl4Spec.State Unit} {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation}
    {s : S} {res : core.result.Result Unit error.Exc × S × A} (h : TopPostDM (L := L) σ blk call don m s res) :
    TopPostDF (L := L) σ blk call don m s res := by
  rcases h with h | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7, h8⟩
  · exact Or.inl h
  · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7, h8.1.1⟩

/-- The statement for one cap, with the domain schedule and the frame
invariant. -/
abbrev DecOKDM (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostDM (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ⦄

/-- **`DecOKM` with the domain schedule**, from the cap's `DomFrame`. -/
theorem DecOKM.withDom {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (h : DecOKM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer)
    (hF : DomFrame (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKDM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer := by
  refine WP.spec_mono (WP.spec_and h hF.1) ?_
  rintro res ⟨hq, hkb, hw⟩
  rcases hq with hq | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7⟩
  · exact Or.inl hq
  · obtain ⟨hl, hst⟩ := hF.2 inv σ1 h1 h2 y hy
    refine Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, ?_, by rw [hkb]; exact h7⟩
    rw [hkb]; exact hDR.frame hw hl hst

/-- The null and zombie caps: `InvalidCapability 0`, the state unchanged. -/
theorem decOKM_invalid (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (cap : capability.Cap)
    (hc : cap = .Null ∨ ∃ p zt n, cap = .Zombie p zt n)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer := by
  rcases hc with rfl | ⟨p, zt, n, rfl⟩ <;>
  · unfold DecOKM syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **The dispatch of `decode_invocation` with the domain schedule and the
frame invariant**: from one statement per cap (`DecOKDM`), the null and
zombie caps aside. -/
theorem decode_invocation_refinesDM (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (cap : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef)
    (hK : ∀ c, cap = c → (∀ p zt n, c ≠ .Zombie p zt n) → c ≠ .Null →
      DecOKDM (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKDM (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer := by
  by_cases hn : cap = .Null
  · subst hn
    unfold DecOKDM syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩
  by_cases hz : ∃ p zt n, cap = .Zombie p zt n
  · obtain ⟨p, zt, n, rfl⟩ := hz
    unfold DecOKDM syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩
  exact hK cap rfl (fun p zt n e => hz ⟨p, zt, n, e⟩) hn

end

/-! ## The statement -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The related states: a placed typed heap and a ghost tree with the CSpace
relation (with `MdbInv`), `FinInv` and the domain schedule. -/
def RelTopM (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ th G, Placed th ∧ CRel th (L.mem s) σ G ∧ FinInv th (L.mem s) σ G ∧ DomRel (L.mem s) (L.ksb s) σ ∧
    MdbOKV (L.ksb s) (L.mem s) G

/-- **The message-register and reply writes** (for the IPC proofs): from
related states, FL4's success tail (the reply when called, then
`Running`, if the thread is still `Restart`) against the spec's, and FL4's
error reply against `reply_from_kernel (msg_from_syscall_error e)` when
called. -/
structure ReplyHypM (ct : U64) (is_call : Bool) : Prop where
  succ : ∀ (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit) (rr : List Fl4Spec.Data), RelTopM (L := L) s1 σ' →
    flTail (st := st) ct is_call s1 a1 ⦃ res => res.1 = .Ok () ∧
      ∃ z ∈ (specTail is_call ct.bv rr σ').1, RelTopM (L := L) res.2.1 z.2 ⦄
  fail : ∀ (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit) (e : error.SysError) (e' : Fl4Spec.SyscallError),
    RelTopM (L := L) s1 σ' → ErrRel (.Sys e) e' →
    ((if is_call then do
        let s2 ← syscall.reply_error st s1 ct e
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ z ∈ ((Fl4Spec.NonDet.when is_call <|
        Fl4Spec.replyFromKernel ct.bv (Fl4Spec.msgFromSyscallError e')) σ').1, RelTopM (L := L) res.2.1 z.2 ⦄

/-- **The fault handler** (for the IPC proofs): FL4's `handle_fault` of `f`
against the spec's of `f'`, from the state of the lookup. -/
def FaultHypAtM (s : S) (σ : Fl4Spec.State Unit) (ct : U64) (f : error.Fault) (f' : Fl4Spec.Fault) : Prop :=
  ∀ a : A, faults.handle_fault st arI s a ct f ⦃ r =>
    ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1, RelTopM (L := L) r.1 z.2 ⦄

/-- **The result of `handle_invocation`**: an outcome of
`fl4HandleInvocation` of FL4's kind, with the states related. -/
def HIPostM (σ : Fl4Spec.State Unit) (calling blocking canDonate firstPhase : Bool) (cptr : Fl4Spec.CapRef)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ y ∈ ((Fl4Spec.fl4HandleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr).run σ).1,
    ((res.1 = .Ok () ∧ y.1 = .ok ()) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
    RelTopM (L := L) res.2.1 y.2

/-- **The result of a decode that replies itself** (an `In` called): the
spec's error with the state unchanged, or FL4 is done and its thread no
longer `Restart`, and the spec's decode, restart, invocation and success
tail have an outcome related to FL4's state. -/
def TopPostRM (σ : Fl4Spec.State Unit) (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (ct : U64) (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧
  ∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1 ∧
      ∃ z ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) res.2.1 z.2

/-- The statement for one cap whose decode replies itself. -/
abbrev DecOKRM (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostRM (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) ct s res ⦄

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's `handle_invocation` refines l4v's `handle_invocation` with FL4's
dispatcher** (see the module docstring): from related states, the
front end's reads (`HIRead`, the explicit values `info` .. `args` with
their hypotheses), the decode and invocation of the cap at the looked-up
slot (`hDec`, as `decode_invocation_refinesD` gives it), the reply writes
(`ReplyHypM`) and the fault handler (`FaultHypAtM`, for the lookup's fault
and the extra caps'). -/
theorem handle_invocation_refinesM (s : S) (ar : A) (σ : Fl4Spec.State Unit) (th : TypedHeap) (G : MdbGhost)
    (hP : Placed th) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hDR : DomRel (L.mem s) (L.ksb s) σ) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    -- the front end's reads (`HIRead`)
    (info : msginfo.MessageInfo) (hinfo : msg.msg_info st s ct = ok info)
    (mi : Fl4Spec.MessageInfo) (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    (buf : U64) (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    (buffer : Option Fl4Spec.ObjRef)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr)))
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (hrr : (∃ e exs, r2 = .Ok e ∧ er = .ok exs) ∨
      (∃ f f', r2 = .Err f ∧ er = .error f' ∧ (blocking = true → FaultHypAtM (L := L) arI s σ ct f f')))
    (args : List Fl4Spec.Data) (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False))
    -- the fault of a failed lookup
    (hFL : blocking = true → ∀ lf lf', LookupFaultRel lf lf' →
      FaultHypAtM (L := L) arI s σ ct (.Cap cptr false lf)
        (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) false lf'))
    -- the reply writes
    (hRep : ReplyHypM (L := L) ct is_call (A := A))
    -- the decode and invocation of the cap
    (hDec : ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), capAt (L.mem s) (cslotAddr sl) = ok c →
      Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →
      DecOKDM (L := L) arI s ar σ info.label (msgLen info buf) (cslotAddr sl) c blocking is_call can_donate first_phase
        buf e mi.miLabel args (Fl4Spec.toBl cptr.bv) sl exs buffer ∨
      DecOKRM (L := L) arI s ar σ info.label (msgLen info buf) (cslotAddr sl) c blocking is_call can_donate first_phase
        buf e mi.miLabel args (Fl4Spec.toBl cptr.bv) sl exs buffer ct) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostM (L := L) σ is_call blocking can_donate first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  have hRT0 : RelTopM (L := L) s σ := ⟨th, G, hP, hCR, hFI, hDR, hFR⟩
  unfold syscall.handle_invocation
  rw [hct]; simp only [bind_ok, hinfo]
  refine WP.spec_bind (lookup_slot_refines (Z := Unit) th s σ hCR.1 hCR.2.1 ct htcb cptr) ?_
  rintro r ⟨e, he, hrel, hok⟩
  cases r with
  | Err lf =>
    cases e with
    | ok v => exact hrel.elim
    | error lf' =>
      simp only
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.error lf', σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot; exact run_bind_error (s := σ) he _
      have hmF := hiMF_lookup_err (mi := mi) hl
      cases blocking
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨(.ok (), σ), hi_mem hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
          (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0⟩
      · simp only [↓reduceIte]
        refine WP.spec_bind (hFL rfl lf lf' hrel ar) ?_
        rintro ⟨s1, a1⟩ ⟨z, hz, hRT⟩
        refine (WP.spec_ok _).2 ?_
        exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
          Or.inl ⟨rfl, rfl⟩, hRT⟩
  | Ok r1 =>
    cases e with
    | error lf' => exact hrel.elim
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth⟩ := hok
      obtain ⟨c, a, hc, hca, hget⟩ := hCR.1.slot_cap hp hth
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.ok (a, sl), σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot
        rw [run_bind_ok he]
        simp only
        rw [run_bind_ok (run_liftE hget)]
        rfl
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, hbuf, hr2]
      rcases hrr with ⟨ex, exs, rfl, rfl⟩ | ⟨f, f', rfl, rfl, hfh⟩
      · simp only
        rw [msgLen_eq]; simp only [bind_ok]
        have hca' : absCap c = a := hca.2
        subst hca'
        have hmF := hiMF_ok (mi := mi) hl hbuffer her
        have hmE := hiME_run (cptr := Fl4Spec.toBl cptr.bv) (fp := first_phase) (a := absCap c) (sl := sl)
          (exs := exs) hmrs
        rcases hDec sl c ex exs hc hget rfl rfl with hD | hD
        swap
        · refine WP.spec_bind hD ?_
          rintro ⟨r3, s1, a1⟩ (⟨e3, he3, hs1, e', hdec, herr⟩ | ⟨hok3, hne, inv, hdec, σ1, hst, rr, σy, hy, z, hz, hRT⟩)
          · simp only at he3 hs1
            subst he3 hs1
            cases e3 with
            | Sys e2 =>
              refine WP.spec_mono (hRep.fail _ a1 σ e2 e' hRT0 herr) ?_
              rintro res ⟨hres, z, hz, hRT⟩
              exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
                Or.inl ⟨hres, rfl⟩, hRT⟩
            | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          simp only at hok3; subst hok3
          refine WP.spec_bind (tcb_state_spec' (st := st) s1 ct) ?_
          rintro v rfl
          rw [if_neg hne]
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
            (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨rfl, rfl⟩, hRT⟩
        refine WP.spec_bind hD ?_
        rintro ⟨r3, s1, a1⟩ hq
        rcases hq with ⟨e3, he3, hs1, e', hdec, herr⟩ |
            ⟨inv, hdec, σ1, hst, y, hy, th', G', hcase, hP', hCR', hFI', hDR', hFR'⟩
        · simp only at he3 hs1
          subst he3 hs1
          cases e3 with
          | Sys e2 =>
            refine WP.spec_mono (hRep.fail _ a1 σ e2 e' hRT0 herr) ?_
            rintro res ⟨hres, z, hz, hRT⟩
            exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
              Or.inl ⟨hres, rfl⟩, hRT⟩
          | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
        · rcases hcase with ⟨hok3, rr, hyr⟩ | ⟨hpre, hyr⟩
          · simp only at hok3
            subst hok3
            refine WP.spec_mono (hRep.succ s1 a1 y.2 rr ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩) ?_
            rintro res ⟨hres, z, hz, hRT⟩
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨hres, rfl⟩, hRT⟩
          · simp only at hpre
            subst hpre
            refine (WP.spec_ok _).2 ?_
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.error (), y2), hi_mem hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_pre (by rw [← hcur]; exact hst) hy)), Or.inr ⟨rfl, rfl⟩,
              ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩⟩
      · simp only
        have hmF := hiMF_extra_err (cptr := Fl4Spec.toBl cptr.bv) hl hbuffer her
        cases blocking
        · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨(.ok (), σ), hi_mem hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
            (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0⟩
        · simp only [↓reduceIte]
          refine WP.spec_bind (hfh rfl ar) ?_
          rintro ⟨s1, a1⟩ ⟨z, hz, hRT⟩
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
            Or.inl ⟨rfl, rfl⟩, hRT⟩

end


/-! ## `In` called, with the MDB invariants -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The `In` access and its reply** (for the IPC proofs and the arch
backend): FL4's `In` of `size` bytes at `port`, called, against the spec's
restart, `In` invocation and success tail: FL4 is done, its thread no longer
`Restart`, and the spec has an outcome related to FL4's state. -/
def PortInCallHypM (s : S) (σ : Fl4Spec.State Unit) (ar : A) (ct port size : U64) (d : Fl4Spec.IoPortInvocationData) :
    Prop :=
  portInTail (st := st) arI s ar ct port size true ⦃ res => res.1 = .Ok () ∧
    L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
      ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) d))).run σ1).1 ∧
      ∃ z ∈ (specTail true ct.bv rr σy).1, RelTopM (L := L) res.2.1 z.2 ⦄

/-- **IOPort `In` called** (labels 64..66, `call` true): `DecOKRM`, the reply
being FL4's own (`PortInCallHypM`). -/
theorem decode_invocation_ioport_in_callM (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (hl : 64 ≤ lbl.val ∧ lbl.val ≤ 66)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel (inLabel (portSz lbl)))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) {tcb : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb tcb))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536)
    (hIn : ∀ port : U64, port.val < 65536 →
      PortInCallHypM (L := L) arI s σ ar ct port ⟨BitVec.ofNat 64 (portSz lbl)⟩ (inData (portSz lbl)))
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKRM (L := L) arI s ar σ lbl length slot (.IoPort first last 0#u64) blk true don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  unfold DecOKRM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hsz : portSz lbl = 1 ∨ portSz lbl = 2 ∨ portSz lbl = 4 := by unfold portSz; split_ifs <;> simp
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl (.IoPort first last 0#u64) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec
        (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
          (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val)))) := rfl
  rw [hspec, decode_in_eq slbl _ _ hsz hlbl]
  unfold ioport.decode
  simp only
  rw [hct, port_size_eq lbl ⟨hl.1, by omega⟩, is_port_in_eq lbl ⟨hl.1, by omega⟩]
  simp only [bind_ok]
  have hszU : (if lbl.val = 64 ∨ lbl.val = 67 then 1#u64 else if lbl.val = 65 ∨ lbl.val = 68 then 2#u64
      else 4#u64) = ⟨BitVec.ofNat 64 (portSz lbl)⟩ := by
    unfold portSz; split_ifs <;> rfl
  rw [hszU]
  have hsz0 : ¬ (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64) = 0#u64 := by
    rw [u64_eq_iff]; show ¬ (BitVec.ofNat 64 (portSz lbl)).toNat = 0
    rcases hsz with h | h | h <;> rw [h] <;> decide
  rw [if_neg hsz0, decide_eq_true (by omega : lbl.val ≤ 66)]
  simp only [↓reduceIte]
  -- the argument
  by_cases h1 : length < 1#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, .truncatedMessage, run_liftME_err (run_liftME_err ?_), Or.inl trivial⟩
    unfold Fl4Spec.argsAtLeast
    rw [whenE_pos (show 1 > (args.map UScalar.bv).length by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  rw [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), lift, bind_ok]
  unfold Fl4Spec.argsAtLeast
  rw [whenE_neg (show ¬ 1 > ((y0 :: rest).map UScalar.bv).length by simp), retOk_bind, retOk_bind]
  have hmap : List.map UScalar.bv (y0 :: rest) = y0.bv :: rest.map UScalar.bv := rfl
  have g0 : (y0.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  rw [hmap, g0, the_some]
  set port := y0 &&& 65535#u64 with hport
  have hpv : port.val < 65536 := by rw [hport, and_ffff]; omega
  have hp16 : (Fl4Spec.ucast 16 y0.bv : BitVec 16) = BitVec.ofNat 16 port.val := by
    apply BitVec.eq_of_toNat_eq; rw [ucast16_toNat, BitVec.toNat_ofNat, hport, and_ffff]; omega
  rw [hp16]
  have hszv : (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64).val = portSz lbl := by
    show (BitVec.ofNat 64 (portSz lbl)).toNat = _
    rw [BitVec.toNat_ofNat]; rcases hsz with h | h | h <;> rw [h]
  rw [allowed_eq first last port _ hl16 hpv (by rw [hszv]; exact hsz)]
  simp only [hszv, bind_ok]
  have hens := ensure_run first last hfl hl16 port hpv hsz σ
  by_cases hc : port.val < first.val ∨ port.val + portSz lbl - 1 > last.val
  · rw [if_pos hc]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok]
    rw [if_pos hc] at hens
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, .illegalOperation, run_liftME_err (run_liftME_err (run_bind_error hens _)),
      Or.inl trivial⟩
  rw [if_neg hc]
  rw [if_neg hc] at hens
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_mono (hIn port hpv) ?_
  rintro res ⟨hres, hne, hall⟩
  obtain ⟨σ1, hst, -⟩ := setThreadState_eq σ ct.bv tcb hkt .restart
  obtain ⟨rr, σy, hy, z, hz, hRT⟩ := hall σ1 hst
  refine Or.inr ⟨hres, hne, .invokeArchObject (.spec (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val)
    (inData (portSz lbl))))), ?_, σ1, by rw [hcur]; exact hst, rr, σy, hy, z, hz, hRT⟩
  exact DecOut.of_eq (run_liftME_ok (run_liftME_ok ((run_bind_ok hens _).trans rfl)))

end

end

end Fl4Proofs.P3
