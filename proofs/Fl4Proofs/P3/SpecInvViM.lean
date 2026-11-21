/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi3): **`viGap : ViGap`** (vi2's remaining
obligation) and the tops **`kentry_validIdle` / `kcall_validIdle`** (spec side only; imports
SpecInvViL).

* `ne_tc` / `ne_sc`: a held thread cap does not name `N` (the entry's `IO (fun _ => N)`,
  sg1's `IdleOutV`), a held SC cap does not name `S` (`IrqOutV (fun _ => S)`, vi2's
  `IdleScOutV`); l4v `valid_global_refs` (idle_thread_ptr, idle_sc_ptr ∈ global_refs).
* `TcbNe` / `ScNe` (`tcbNe_of` / `scNe_of` from SpecInvViK's `TgOK`).
* invoke_tcb, one lemma per arm (`vi_tcb*`; `threadControlCaps` / `threadControlSched`
  start with the cap installs at `VO`), the dispatcher `vi_invokeTcbG`;
  invoke_sched_context per arm (`vi_sc*`), `vi_invokeSc`.
* **`viGap`**: untyped (`vi_invokeUntyped`: the held untyped's region ∌ N, S; ut8's decode
  facts `GapOKN`), MakePool (`vi_makePool`: the parent untyped's region), TCB and SC
  (decode target facts `tgOK_of`).
* Tops: `kentry_validIdle := kentry_validIdle_of viGap`, `kcall_validIdle`.
-/
import Fl4Proofs.P3.SpecInvViL
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

/-! ## Held caps name neither idle object -/

theorem ne_tc {σ : State Unit} (hO : IO (fun _ => N) σ) {t : ObjRef} (h : Held (uV σ) (.threadCap t)) : t ≠ N := by
  rintro rfl
  obtain ⟨s, hs⟩ := h
  exact hO 0 s _ hs (by simp [covR, capRng, objRefs])

theorem ne_sc {σ : State Unit} (hS : IrqOutV (fun _ => S) (uV σ)) {c : ObjRef} {sz : Nat}
    (h : Held (uV σ) (.schedContextCap c sz)) : c ≠ S := by
  rintro rfl
  obtain ⟨s, hs⟩ := h
  exact hS 0 s _ hs (by simp [covR, capRng, objRefs])

/-- What the TCB performs need. -/
def TcbNe (N S : ObjRef) : TcbInvocation → Prop
  | .readRegisters s _ _ _ => s ≠ N
  | .copyRegisters _ s _ _ _ _ _ => s ≠ N
  | .threadControlSched t _ _ _ _ sc => t ≠ N ∧ ∀ c, sc = some (some c) → c ≠ S
  | .suspend t => t ≠ N
  | .notificationControl t _ => t ≠ N
  | _ => True

/-- What the SC performs need. -/
def ScNe (N S : ObjRef) : SchedContextInvocation → Prop
  | .invokeSchedContextBind p c => p ≠ S ∧ ∀ t, c = .threadCap t → t ≠ N
  | .invokeSchedContextUnbindObject p _ => p ≠ S
  | _ => True

theorem tcbNe_of {σ : State Unit} (hO : IO (fun _ => N) σ) (hS : IrqOutV (fun _ => S) (uV σ))
    {i : TcbInvocation} (h : TcbTg (uV σ) i) : TcbNe N S i := by
  cases i with
  | readRegisters s _ _ _ => exact ne_tc hO h
  | copyRegisters _ s _ _ _ _ _ => exact ne_tc hO h
  | threadControlSched t _ _ _ _ sc =>
    exact ⟨ne_tc hO h.1, fun c hc => by obtain ⟨sz, hh⟩ := h.2 c hc; exact ne_sc hS hh⟩
  | suspend t => exact ne_tc hO h
  | notificationControl t _ => exact ne_tc hO h
  | _ => trivial

theorem scNe_of {σ : State Unit} (hO : IO (fun _ => N) σ) (hS : IrqOutV (fun _ => S) (uV σ))
    {i : SchedContextInvocation} (h : ScTg (uV σ) i) : ScNe N S i := by
  cases i with
  | invokeSchedContextBind p c =>
    obtain ⟨⟨sz, hp⟩, hc⟩ := h
    exact ⟨ne_sc hS hp, fun t e => ne_tc hO (e ▸ hc)⟩
  | invokeSchedContextUnbindObject p c =>
    obtain ⟨sz, hp⟩ := h
    exact ne_sc hS hp
  | _ => trivial

/-! ## invoke_tcb -/

theorem vi_of_vo_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKE (VO N S b) m) (hg : ∀ a, IKE (VI N S b) (g a)) :
    ∀ σ, VO N S b σ → ∀ y ∈ ((m >>= g).run σ).1, VI N S b y.2 := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · obtain ⟨r, s⟩ := z
    simp only at ha; subst ha
    exact hg a s (hm σ hσ _ hz).1 y hy
  · exact (hm σ hσ z hz).1

theorem vi_tcbSuspend (t : ObjRef) (ht : t ≠ N) : IKE (VI N S true) (invokeTcb (Z := Unit) (.suspend t)) := by
  simp only [invokeTcb]; vi_auto

theorem vi_tcbResume (t : ObjRef) : IKE (VI N S true) (invokeTcb (Z := Unit) (.resume t)) := by
  simp only [invokeTcb]; vi_auto

theorem vo_tcbCaps (t : ObjRef) (sl : CslotPtr) (fh th cr vr : Option (Cap × CslotPtr))
    (bf : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (VO N S b) (invokeTcb (Z := Unit) (.threadControlCaps t sl fh th cr vr bf)) := by
  simp only [invokeTcb]
  exact ike_bind (vo_installTcbCap _ _ _ _) fun _ => ike_bind (vo_installTcbCap _ _ _ _) fun _ =>
    ike_bind (vo_installTcbCap _ _ _ _) fun _ => ike_bind (vo_installTcbCap _ _ _ _) fun _ =>
    ike_bind (vo_installTcbFrameCap _ _ _) fun _ => ike_returnOk _

theorem vi_tcSched (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr)) (mcp prio : Option (Word8 × ObjRef))
    (sc : Option (Option ObjRef)) (ht : t ≠ N) (hsc : ∀ c, sc = some (some c) → c ≠ S) :
    ∀ σ, VO N S true σ → ∀ y ∈ ((invokeTcb (Z := Unit) (.threadControlSched t sl fh mcp prio sc)).run σ).1,
      VI N S true y.2 := by
  simp only [invokeTcb]
  refine vi_of_vo_bind (vo_installTcbCap _ _ _ _) fun _ => ?_
  rcases sc with _ | _ | c
  · clear hsc; vi_auto
  · clear hsc; vi_auto
  · have hc := hsc c rfl
    clear hsc
    vi_auto

theorem vi_tcbCopy (d s : ObjRef) (a1 a2 a3 a4 : Bool) (ar : ArchCopyRegisterSets) (hs : s ≠ N) :
    IKE (VI N S true) (invokeTcb (Z := Unit) (.copyRegisters d s a1 a2 a3 a4 ar)) := by
  simp only [invokeTcb]; vi_auto

theorem vi_tcbRead (s : ObjRef) (a : Bool) (n : Word) (ar : ArchCopyRegisterSets) (hs : s ≠ N) :
    IKE (VI N S true) (invokeTcb (Z := Unit) (.readRegisters s a n ar)) := by
  simp only [invokeTcb]; vi_auto

theorem vi_tcbWrite (d : ObjRef) (a : Bool) (vs : List Word) (ar : ArchCopyRegisterSets) :
    IKE (VI N S true) (invokeTcb (Z := Unit) (.writeRegisters d a vs ar)) := by
  simp only [invokeTcb]; vi_auto

theorem vi_tcbBindN (t n : ObjRef) (ht : t ≠ N) :
    IKE (VI N S true) (invokeTcb (Z := Unit) (.notificationControl t (some n))) := by
  simp only [invokeTcb]; vi_auto

theorem vi_tcbUnbindN (t : ObjRef) : IKE (VI N S true) (invokeTcb (Z := Unit) (.notificationControl t none)) := by
  simp only [invokeTcb]; vi_auto

theorem vi_tcbTls (t : ObjRef) (v : Word) : IKE (VI N S true) (invokeTcb (Z := Unit) (.setTLSBase t v)) := by
  simp only [invokeTcb]; vi_auto

theorem vi_tcbFlags (t : ObjRef) (c s : TcbFlags) : IKE (VI N S true) (invokeTcb (Z := Unit) (.setFlags t c s)) := by
  simp only [invokeTcb]; vi_auto

/-- **invoke_tcb** from the decode's target facts. -/
theorem vi_invokeTcbG (i : TcbInvocation) (h : TcbNe N S i) :
    ∀ σ, VO N S true σ → ∀ y ∈ ((invokeTcb (Z := Unit) i).run σ).1, VI N S true y.2 := by
  intro σ hσ y hy
  cases i with
  | suspend t => exact vi_tcbSuspend t h σ hσ.1 y hy
  | resume t => exact vi_tcbResume t σ hσ.1 y hy
  | threadControlCaps t sl fh th cr vr bf => exact (vo_tcbCaps t sl fh th cr vr bf σ hσ y hy).1
  | threadControlSched t sl fh mcp prio sc => exact vi_tcSched t sl fh mcp prio sc h.1 h.2 σ hσ y hy
  | copyRegisters d s a1 a2 a3 a4 ar => exact vi_tcbCopy d s a1 a2 a3 a4 ar h σ hσ.1 y hy
  | readRegisters s a n ar => exact vi_tcbRead s a n ar h σ hσ.1 y hy
  | writeRegisters d a vs ar => exact vi_tcbWrite d a vs ar σ hσ.1 y hy
  | notificationControl t n =>
    rcases n with _ | n
    · exact vi_tcbUnbindN t σ hσ.1 y hy
    · exact vi_tcbBindN t n h σ hσ.1 y hy
  | setTLSBase t v => exact vi_tcbTls t v σ hσ.1 y hy
  | setFlags t c s => exact vi_tcbFlags t c s σ hσ.1 y hy

/-! ## invoke_sched_context -/

theorem vi_scConsumed (p : ObjRef) :
    IK (VI N S true) (invokeSchedContext (Z := Unit) (.invokeSchedContextConsumed p)) := by
  simp only [invokeSchedContext]; vi_auto

theorem vi_scBind (p : ObjRef) (c : Cap) (hp : p ≠ S) (hc : ∀ t, c = .threadCap t → t ≠ N) :
    IK (VI N S true) (invokeSchedContext (Z := Unit) (.invokeSchedContextBind p c)) := by
  cases c
  case threadCap t =>
    have ht := hc t rfl
    clear hc
    simp only [invokeSchedContext]; vi_auto
  all_goals clear hc; simp only [invokeSchedContext]; vi_auto

theorem vi_scUnbindObj (p : ObjRef) (c : Cap) (hp : p ≠ S) :
    IK (VI N S true) (invokeSchedContext (Z := Unit) (.invokeSchedContextUnbindObject p c)) := by
  cases c
  all_goals simp only [invokeSchedContext]; vi_auto

theorem vi_scUnbind (p : ObjRef) :
    IK (VI N S true) (invokeSchedContext (Z := Unit) (.invokeSchedContextUnbind p)) := by
  simp only [invokeSchedContext]; vi_auto

theorem vi_scYieldTo (p : ObjRef) :
    IK (VI N S true) (invokeSchedContext (Z := Unit) (.invokeSchedContextYieldTo p)) := by
  simp only [invokeSchedContext]; exact vi_schedContextYieldTo p

/-- **invoke_sched_context** from the decode's target facts. -/
theorem vi_invokeSc (i : SchedContextInvocation) (h : ScNe N S i) :
    IK (VI N S true) (invokeSchedContext (Z := Unit) i) := by
  cases i with
  | invokeSchedContextConsumed p => exact vi_scConsumed p
  | invokeSchedContextBind p c => exact vi_scBind p c h.1 h.2
  | invokeSchedContextUnbindObject p c => exact vi_scUnbindObj p c h
  | invokeSchedContextUnbind p => exact vi_scUnbind p
  | invokeSchedContextYieldTo p => exact vi_scYieldTo p

/-! ## The gap -/

theorem viGap_arch (ai : Fl4ArchInvocation) (hg : ViGapInv (.invokeArchObject ai)) :
    ∃ f s p bs, ai = .spec (.invokeASIDControl (.makePool f s p bs)) := by
  cases ai
  case spec i =>
    cases i
    case invokeASIDControl a =>
      cases a
      exact ⟨_, _, _, _, rfl⟩
    all_goals exact (hg : False).elim
  all_goals exact (hg : False).elim

/-- **vi2's remaining obligation, proved.** -/
theorem viGap : ViGap := by
  intro N S blk call don inv σ hg hV hO hS hU hD
  have ht : TgOK (uV σ) inv := tgOK_of hD
  have hf : GapOKN (uV σ) inv := by
    obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
    exact okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv inv s0 hmem
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact vi_invokeUntyped ui σ hV hU.ut'.ut (by cases ui; exact hf.1)
      (fun s d bb n fi hc => ⟨hO 0 s _ hc, hS 0 s _ hc⟩) z hz
  | invokeTCB i =>
    simp only [fl4PerformInvocation] at hy
    exact vi_invokeTcbG i (tcbNe_of hO hS ht) σ ⟨hV, hO⟩ y hy
  | invokeSchedContext i =>
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact vi_invokeSc i (scNe_of hO hS ht) σ hV x hx
  | invokeArchObject ai =>
    obtain ⟨frame, slot, parent, base, rfl⟩ := viGap_arch ai hg
    obtain ⟨⟨dev, fi, hc, -⟩, -, -⟩ := hf
    have hfr : frame ∈ delR frame page_bits := by
      obtain ⟨hn, hfit⟩ := UtWf.fit (σ := σ) hU.ut'.ut.2.1 hc
      exact (mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
    simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    obtain ⟨z, hz, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    exact vi_makePool frame slot parent base σ hV (hO 0 parent _ hc) (hS 0 parent _ hc) hfr z hz
  | _ => exact (hg : False).elim

/-! ## The tops -/

/-- **valid_idle across the syscall entry.** Premises: `ValidIdle` (carried here),
`SpecGlobS ∧ IdleOutV` (sg1, carried), `IdleScOutV` (carried here), `UtInv3` (ut8, carried),
`ha` (ct active, as nq3), **`CtSc` [J]** for the pinned syscalls only (vi2). -/
theorem kentry_validIdle (c : Syscall) {σ : State Unit} (hV : ValidIdle σ)
    (hS : SInvG.SpecGlobS σ ∧ SInvG.IdleOutV σ) (hI : IdleScOutV σ) (hU : UtInv3 σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) (hct : Pinned c → CtSc σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ValidIdle y.2 ∧ IdleScOutV y.2 :=
  kentry_validIdle_of viGap c hV hS hI hU ha hct

/-- **valid_idle across every kernel event.** -/
theorem kcall_validIdle (rep : Bool) (ev : Event) {σ : State Unit} (hV : ValidIdle σ)
    (hS : SInvG.SpecGlobS σ ∧ SInvG.IdleOutV σ) (hI : IdleScOutV σ) (hU : UtInv3 σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hct : ∀ c, ev = .syscallEvent c → Pinned c → CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ValidIdle y.2 ∧ IdleScOutV y.2 :=
  kcall_validIdle_of viGap rep ev hV hS hI hU ha hct

end

end Fl4Proofs.P3.SInvI
