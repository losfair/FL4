/-
P3 (DESIGN.md §9), IO ports: **IOPort `In`/`Out`** (FL4 `ioport::decode`,
labels 64..69) against l4v `decode_port_invocation`: the same error with the
state unchanged, or the spec's invocation `IOPortInvocation port data`, with
FL4's port operation (`port_in` / `port_out`, arch operations) on that port,
size and data, and (for `Out`, and `In` without a reply) the slots kept.

The IO port cap's range is ordered (`first ≤ last`, as `Issue` makes it;
l4v asserts it).
-/
import Fl4Proofs.P3.IoControl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The spec's `In` label of an access size. -/
def inLabel : Nat → Fl4Spec.ArchInvocationLabel
  | 1 => .x64IOPortIn8 | 2 => .x64IOPortIn16 | _ => .x64IOPortIn32

/-- The spec's `Out` label of an access size. -/
def outLabel : Nat → Fl4Spec.ArchInvocationLabel
  | 1 => .x64IOPortOut8 | 2 => .x64IOPortOut16 | _ => .x64IOPortOut32

/-- The spec's `In` data of an access size. -/
def inData : Nat → Fl4Spec.IoPortInvocationData
  | 1 => .ioPortIn8 | 2 => .ioPortIn16 | _ => .ioPortIn32

/-- The spec's `Out` data of an access size, from the argument word. -/
def outData (raw : Fl4Spec.Data) : Nat → Fl4Spec.IoPortInvocationData
  | 1 => .ioPortOut8 (Fl4Spec.ucast 8 raw) | 2 => .ioPortOut16 (Fl4Spec.ucast 16 raw)
  | _ => .ioPortOut32 (Fl4Spec.ucast 32 raw)

theorem retOk_bind {σ ε α β : Type} (x : α) (f : α → Fl4Spec.NonDetE σ ε β) :
    (Fl4Spec.NonDetE.returnOk x >>= f) = f x := by
  show ExceptT.bind (ExceptT.pure x) f = f x
  simp only [ExceptT.bind, ExceptT.pure, ExceptT.mk]
  exact nd_pure_bind _ _

theorem decode_in_eq (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (cap : Fl4Spec.ArchCap) {sz : Nat}
    (hsz : sz = 1 ∨ sz = 2 ∨ sz = 4) (h : Fl4Spec.invocationType slbl = .archInvocationLabel (inLabel sz)) :
    Fl4Spec.decodePortInvocation (Z := Unit) slbl args cap =
      (do
        Fl4Spec.argsAtLeast 1 args
        let port ← Fl4Spec.NonDetE.returnOk (Fl4Spec.ucast 16 (Fl4Spec.the args[0]?))
        Fl4Spec.ensurePortOperationAllowed cap (Fl4Spec.ucast 32 port) sz
        Fl4Spec.NonDetE.returnOk (.invokeIOPort (.ioPortInvocation port (inData sz)))) := by
  unfold Fl4Spec.decodePortInvocation
  rcases hsz with rfl | rfl | rfl <;> rw [h] <;> rfl

theorem decode_out_eq (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (cap : Fl4Spec.ArchCap) {sz : Nat}
    (hsz : sz = 1 ∨ sz = 2 ∨ sz = 4) (h : Fl4Spec.invocationType slbl = .archInvocationLabel (outLabel sz)) :
    Fl4Spec.decodePortInvocation (Z := Unit) slbl args cap =
      (do
        Fl4Spec.argsAtLeast 2 args
        let port ← Fl4Spec.NonDetE.returnOk (Fl4Spec.ucast 16 (Fl4Spec.the args[0]?))
        Fl4Spec.ensurePortOperationAllowed cap (Fl4Spec.ucast 32 port) sz
        Fl4Spec.NonDetE.returnOk (.invokeIOPort (.ioPortInvocation port (outData (Fl4Spec.the args[1]?) sz)))) := by
  unfold Fl4Spec.decodePortInvocation
  rcases hsz with rfl | rfl | rfl <;> rw [h] <;> simp only [retOk_bind] <;> rfl

theorem assertE_run {σ' ε : Type} {P : Prop} (h : P) (s : σ') :
    (Fl4Spec.NonDetE.assertE (ε := ε) P).run s = ({(.ok (), s)}, False) := by
  unfold Fl4Spec.NonDetE.assertE
  exact run_liftE (by simp [Fl4Spec.NonDet.assert, h])

/-- The spec's port check, for an ordered range and a port. -/
theorem ensure_run (f l : U64) (hfl : f.val ≤ l.val) (hl : l.val < 65536) (port : U64) (hp : port.val < 65536)
    {sz : Nat} (hsz : sz = 1 ∨ sz = 2 ∨ sz = 4) (σ : Fl4Spec.State Unit) :
    (Fl4Spec.ensurePortOperationAllowed (Z := Unit) (.ioPortCap (BitVec.ofNat 16 f.val) (BitVec.ofNat 16 l.val))
      (Fl4Spec.ucast 32 (BitVec.ofNat 16 port.val)) sz).run σ =
      ({(if port.val < f.val ∨ port.val + sz - 1 > l.val then .error .illegalOperation else .ok (), σ)}, False) := by
  unfold Fl4Spec.ensurePortOperationAllowed
  have hu16 : (Fl4Spec.ucast 32 (BitVec.ofNat 16 port.val) : BitVec 32).toNat = port.val := by
    simp [Fl4Spec.ucast]; omega
  have hend : (Fl4Spec.ucast 32 (BitVec.ofNat 16 port.val) + BitVec.ofNat 32 sz - 1 : BitVec 32).toNat =
      port.val + sz - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, hu16]
    have : (1 : BitVec 32).toNat = 1 := rfl
    rw [this, BitVec.toNat_ofNat]
    rcases hsz with rfl | rfl | rfl <;> omega
  dsimp only
  rw [retOk_bind]
  have hfl' : BitVec.ofNat 16 f.val ≤ BitVec.ofNat 16 l.val := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [run_bind_ok (assertE_run hfl' σ)]
  have hse : Fl4Spec.ucast 32 (BitVec.ofNat 16 port.val) ≤
      Fl4Spec.ucast 32 (BitVec.ofNat 16 port.val) + BitVec.ofNat 32 sz - 1 := by
    rw [BitVec.le_def, hend, hu16]; rcases hsz with rfl | rfl | rfl <;> omega
  rw [run_bind_ok (assertE_run hse σ)]
  have hc : (Fl4Spec.ucast 32 (BitVec.ofNat 16 port.val) < Fl4Spec.ucast 32 (BitVec.ofNat 16 f.val) ∨
      Fl4Spec.ucast 32 (BitVec.ofNat 16 port.val) + BitVec.ofNat 32 sz - 1 > Fl4Spec.ucast 32 (BitVec.ofNat 16 l.val)) ↔
      (port.val < f.val ∨ port.val + sz - 1 > l.val) := by
    rw [BitVec.lt_def, GT.gt, BitVec.lt_def, hend, hu16]
    simp [Fl4Spec.ucast]; omega
  by_cases h : port.val < f.val ∨ port.val + sz - 1 > l.val
  · rw [whenE_pos (hc.2 h), if_pos h]; rfl
  · rw [whenE_neg (fun h' => h (hc.1 h')), if_neg h]; rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The outcome of an IOPort invocation against a spec decode `m`: the same
error with the state unchanged, or the spec's invocation with `Q`. -/
def PortPost (σ : Fl4Spec.State Unit) (m : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation) (s : S) (ar : A)
    (Q : Fl4Spec.ArchInvocation → S → A → Prop) : core.result.Result Unit error.Exc × S × A → Prop
  | (.Err e, s', a') => s' = s ∧ a' = ar ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e'
  | (.Ok (), s', a') => ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ Q inv s' a'

theorem allowed_eq (first last port size : U64) (hl : last.val < 65536) (hp : port.val < 65536)
    (hsz : size.val = 1 ∨ size.val = 2 ∨ size.val = 4) :
    ioport.allowed first last port size =
      ok (if port.val < first.val ∨ port.val + size.val - 1 > last.val
        then .Err (.Sys .IllegalOperation) else .Ok ()) := by
  unfold ioport.allowed
  simp only [lift, bind_ok]
  have he : (core.num.U64.wrapping_sub (core.num.U64.wrapping_add port size) 1#u64).val = port.val + size.val - 1 := by
    rw [core.num.U64.wrapping_sub_val_eq, core.num.U64.wrapping_add_val_eq]
    simp [U64.size, U64.numBits]; omega
  by_cases h1 : port < first
  · rw [if_pos h1, if_pos (Or.inl (by scalar_tac))]; rfl
  · rw [if_neg h1]
    by_cases h2 : core.num.U64.wrapping_sub (core.num.U64.wrapping_add port size) 1#u64 > last
    · rw [if_pos h2, if_pos (Or.inr (by scalar_tac))]; rfl
    · rw [if_neg h2, if_neg (by scalar_tac)]

theorem port_size_eq (lbl : U64) (h : 64 ≤ lbl.val ∧ lbl.val ≤ 69) :
    ioport.port_size lbl = ok (if lbl.val = 64 ∨ lbl.val = 67 then 1#u64
      else if lbl.val = 65 ∨ lbl.val = 68 then 2#u64 else 4#u64) := by
  unfold ioport.port_size
  have : lbl.val = 64 ∨ lbl.val = 65 ∨ lbl.val = 66 ∨ lbl.val = 67 ∨ lbl.val = 68 ∨ lbl.val = 69 := by omega
  rcases this with h | h | h | h | h | h <;>
    simp [u64_eq_iff, h, fl4_abi.label.X86IOPortIn8, fl4_abi.label.X86IOPortOut8, fl4_abi.label.X86IOPortIn16,
      fl4_abi.label.X86IOPortOut16, fl4_abi.label.X86IOPortIn32, fl4_abi.label.X86IOPortOut32]

theorem is_port_in_eq (lbl : U64) (h : 64 ≤ lbl.val ∧ lbl.val ≤ 69) :
    ioport.is_port_in lbl = ok (decide (lbl.val ≤ 66)) := by
  unfold ioport.is_port_in
  have : lbl.val = 64 ∨ lbl.val = 65 ∨ lbl.val = 66 ∨ lbl.val = 67 ∨ lbl.val = 68 ∨ lbl.val = 69 := by omega
  rcases this with h | h | h | h | h | h <;>
    simp [u64_eq_iff, h, fl4_abi.label.X86IOPortIn8, fl4_abi.label.X86IOPortIn16, fl4_abi.label.X86IOPortIn32]

/-- The access size of an IO port label. -/
def portSz (lbl : U64) : Nat := if lbl.val = 64 ∨ lbl.val = 67 then 1 else if lbl.val = 65 ∨ lbl.val = 68 then 2 else 4

theorem set_thread_state_cpu (s : S) (t v : U64) :
    sched.set_thread_state st s t v ⦃ s' => L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ⦄ :=
  WP.spec_mono (set_thread_state_cases s t v) (by rintro s' (rfl | rfl) <;> simp)

/-- **IOPort `In`** (labels 64..66), without a reply (`call` false: the
reply is `handle_invocation`'s). -/
theorem port_in_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (hl : 64 ≤ lbl.val ∧ lbl.val ≤ 66)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel (inLabel (portSz lbl)))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a')) :
    ioport.decode st arI s ar lbl length (.IoPort first last 0#u64) false buf ⦃ res =>
      PortPost σ (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
        (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val))) s ar
        (fun inv s' a' => ∃ port : U64, port.val < 65536 ∧
          inv = .invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) (inData (portSz lbl))) ∧
          (∃ v, arI.port_in ar port ⟨BitVec.ofNat 64 (portSz lbl)⟩ = ok (v, a')) ∧
          SlotsSame th (L.mem s) (L.mem s')) res ⦄ := by
  have hsz : portSz lbl = 1 ∨ portSz lbl = 2 ∨ portSz lbl = 4 := by unfold portSz; split_ifs <;> simp
  rw [decode_in_eq slbl _ _ hsz hlbl]
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
  · rw [if_pos h1]; simp only [error.truncated, bind_ok, WP.spec_ok]
    refine ⟨rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩
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
  -- the spec's decode, up to the port check
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
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    rw [if_pos hc] at hens
    exact ⟨rfl, rfl, .illegalOperation, run_bind_error hens _, Or.inl trivial⟩
  rw [if_neg hc]
  rw [if_neg hc] at hens
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- `set_thread_state Restart`, the port, `set_thread_state Running`
  refine WP.spec_bind (WP.spec_and (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact)
    (set_thread_state_cpu s ct sched.TS_RESTART)) ?_
  rintro s1 ⟨hS1, hk1, hc1⟩
  obtain ⟨v, a1, hv⟩ := hin ar port ⟨BitVec.ofNat 64 (portSz lbl)⟩
  rw [hv]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, uncurry_apply_pair]
  have hact1 : OutsideObjects th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) := by
    rw [hc1]; simp only [P1.LawfulStore.nodeAt, hk1]; exact hact
  refine WP.spec_bind (set_thread_state_slots th hP s1 ct sched.TS_RUNNING htcb hact1) ?_
  intro s3 hS3
  rw [WP.spec_ok]
  refine ⟨_, run_bind_ok hens _, port, hpv, rfl, ⟨v, hv⟩, hS1.trans hS3⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **IOPort `Out`** (labels 67..69). -/
theorem port_out_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (hl : 67 ≤ lbl.val ∧ lbl.val ≤ 69)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel (outLabel (portSz lbl)))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536) (call : Bool)
    (hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a') :
    ioport.decode st arI s ar lbl length (.IoPort first last 0#u64) call buf ⦃ res =>
      PortPost σ (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
        (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val))) s ar
        (fun inv s' a' => ∃ port data raw : U64, port.val < 65536 ∧
          data.val = raw.val % 2 ^ (8 * portSz lbl) ∧
          inv = .invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) (outData raw.bv (portSz lbl))) ∧
          arI.port_out ar port ⟨BitVec.ofNat 64 (portSz lbl)⟩ data = ok a' ∧
          SlotsSame th (L.mem s) (L.mem s')) res ⦄ := by
  have hsz : portSz lbl = 1 ∨ portSz lbl = 2 ∨ portSz lbl = 4 := by unfold portSz; split_ifs <;> simp
  rw [decode_out_eq slbl _ _ hsz hlbl]
  unfold ioport.decode
  simp only
  rw [hct, port_size_eq lbl ⟨by omega, hl.2⟩, is_port_in_eq lbl ⟨by omega, hl.2⟩]
  simp only [bind_ok]
  have hszU : (if lbl.val = 64 ∨ lbl.val = 67 then 1#u64 else if lbl.val = 65 ∨ lbl.val = 68 then 2#u64
      else 4#u64) = ⟨BitVec.ofNat 64 (portSz lbl)⟩ := by
    unfold portSz; split_ifs <;> rfl
  rw [hszU]
  have hsz0 : ¬ (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64) = 0#u64 := by
    rw [u64_eq_iff]; show ¬ (BitVec.ofNat 64 (portSz lbl)).toNat = 0
    rcases hsz with h | h | h <;> rw [h] <;> decide
  rw [if_neg hsz0, decide_eq_false (by omega : ¬ lbl.val ≤ 66)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : length < 2#u64
  · rw [if_pos h2]; simp only [error.truncated, bind_ok, WP.spec_ok]
    refine ⟨rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩
    unfold Fl4Spec.argsAtLeast
    rw [whenE_pos (show 2 > (args.map UScalar.bv).length by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  rw [if_neg h2]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args with
    | [] | [_] => exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: rest => exact ⟨y0, y1, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), lift, bind_ok]
  unfold Fl4Spec.argsAtLeast
  rw [whenE_neg (show ¬ 2 > ((y0 :: y1 :: rest).map UScalar.bv).length by simp), retOk_bind, retOk_bind]
  have hmap : List.map UScalar.bv (y0 :: y1 :: rest) = y0.bv :: y1.bv :: rest.map UScalar.bv := rfl
  have g0 : (y0.bv :: y1.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  have g1 : (y0.bv :: y1.bv :: rest.map UScalar.bv)[1]? = some y1.bv := rfl
  rw [hmap, g0, g1, the_some, the_some]
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
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    rw [if_pos hc] at hens
    exact ⟨rfl, rfl, .illegalOperation, run_bind_error hens _, Or.inl trivial⟩
  rw [if_neg hc]
  rw [if_neg hc] at hens
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- the data
  have hdata : ∃ data : U64,
      (if (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64) = 1#u64 then ok (y1 &&& 255#u64)
        else if (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64) = 2#u64 then ok (y1 &&& 65535#u64)
        else ok (y1 &&& 4294967295#u64) : Result U64) = ok data ∧ data.val = y1.val % 2 ^ (8 * portSz lbl) := by
    have m8 : (255#u64 : U64).val = 2 ^ 8 - 1 := rfl
    have m16 : (65535#u64 : U64).val = 2 ^ 16 - 1 := rfl
    have m32 : (4294967295#u64 : U64).val = 2 ^ 32 - 1 := rfl
    rcases hsz with h | h | h
    · rw [if_pos (by rw [u64_eq_iff, hszv, h]; rfl)]
      refine ⟨_, rfl, ?_⟩; rw [UScalar.val_and, m8, Nat.and_two_pow_sub_one_eq_mod, h]
    · rw [if_neg (by rw [u64_eq_iff, hszv, h]; decide), if_pos (by rw [u64_eq_iff, hszv, h]; rfl)]
      refine ⟨_, rfl, ?_⟩; rw [UScalar.val_and, m16, Nat.and_two_pow_sub_one_eq_mod, h]
    · rw [if_neg (by rw [u64_eq_iff, hszv, h]; decide), if_neg (by rw [u64_eq_iff, hszv, h]; decide)]
      refine ⟨_, rfl, ?_⟩; rw [UScalar.val_and, m32, Nat.and_two_pow_sub_one_eq_mod, h]
  obtain ⟨data, hd, hdv⟩ := hdata
  rw [hd]; simp only [bind_ok]
  refine WP.spec_bind (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact) ?_
  intro s1 hS1
  obtain ⟨a1, ha1⟩ := hout ar port ⟨BitVec.ofNat 64 (portSz lbl)⟩ data
  rw [ha1]; simp only [bind_ok, WP.spec_ok]
  exact ⟨_, run_bind_ok hens _, port, data, y1, hpv, hdv, rfl, ha1, hS1⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Any other IOPort label**: `IllegalOperation`. -/
theorem port_other_refines (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64) (hl : lbl.val < 64 ∨ 69 < lbl.val)
    (slbl : Fl4Spec.Data)
    (hlbl : ∀ l, Fl4Spec.invocationType slbl = .archInvocationLabel l →
      l ≠ .x64IOPortIn8 ∧ l ≠ .x64IOPortIn16 ∧ l ≠ .x64IOPortIn32 ∧ l ≠ .x64IOPortOut8 ∧ l ≠ .x64IOPortOut16 ∧
      l ≠ .x64IOPortOut32)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List Fl4Spec.Data)
    (first last : U64) (call : Bool) :
    ioport.decode st arI s ar lbl length (.IoPort first last 0#u64) call buf ⦃ res =>
      PortPost σ (Fl4Spec.decodePortInvocation slbl args
        (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val))) s ar (fun _ _ _ => False) res ⦄ := by
  have hz : ioport.port_size lbl = ok 0#u64 := by
    unfold ioport.port_size
    have e : ∀ k : U64, k.val ≠ lbl.val → ¬ lbl = k := fun k hk h => hk (by rw [h])
    rw [if_neg (e _ (by simp [fl4_abi.label.X86IOPortIn8]; omega)),
      if_neg (e _ (by simp [fl4_abi.label.X86IOPortOut8]; omega)),
      if_neg (e _ (by simp [fl4_abi.label.X86IOPortIn16]; omega)),
      if_neg (e _ (by simp [fl4_abi.label.X86IOPortOut16]; omega)),
      if_neg (e _ (by simp [fl4_abi.label.X86IOPortIn32]; omega)),
      if_neg (e _ (by simp [fl4_abi.label.X86IOPortOut32]; omega))]
  unfold ioport.decode
  simp only
  rw [hct, hz]; simp only [bind_ok, ↓reduceIte, error.illegal, WP.spec_ok]
  refine ⟨rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩
  unfold Fl4Spec.decodePortInvocation
  split
  all_goals first
    | rfl
    | (rename_i h; exact absurd rfl ((hlbl _ h).1))
    | (rename_i h; exact absurd rfl ((hlbl _ h).2.1))
    | (rename_i h; exact absurd rfl ((hlbl _ h).2.2.1))
    | (rename_i h; exact absurd rfl ((hlbl _ h).2.2.2.1))
    | (rename_i h; exact absurd rfl ((hlbl _ h).2.2.2.2.1))
    | (rename_i h; exact absurd rfl ((hlbl _ h).2.2.2.2.2))

end

end

end Fl4Proofs.P3
