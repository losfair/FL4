/-
P3 (DESIGN.md §9), invariant line G1 (ctq19): **the syscall entry carries
the ready-queue bundle** (spec side only, outside the JAtZ cone; KENTRY-PLAN
ctq17 handoff 2).

`fl4KernelEntrySyscall true c` reads the current thread `ct`, runs the
`FaultIP` write `fl4SyscallFaultIP ct` (an `as_user` on `ct`) and then
`fl4CallKernel true (.syscallEvent c)`. Every premise of ctq17's
`kcall_tq_sys` is carried across the write to its post-state `w`, with the
entry state of the shell (`σe`) re-based to `w`:

* the family leaves: `tq` / `sa` / `q4` / `rb` / `cs` (EX's SchedQ, T4, RB,
  CurScT), vi's `vi_fl4SyscallFaultIP` (ValidIdle), sb2's `entryOK_keep`
  (EntryOK, as `kentry_scInv_of`), `iu_auto` (Iu), `il` (IL), `js_auto`
  (Js, then `js_rebase`: Js's `σe` only enters through `uV` and `BR`), the
  `uV` frame `uk_fl4SyscallFaultIP` (P3, ScKind, the IrqOutV facts);
* `ik_arch`: an `as_user` only replaces one TCB's `tcbArch`, so every state
  predicate closed under such a replacement is kept (CtQ, Simple, CtExit,
  the current thread active, CtSc, the idle fields, VfhAll via `ti_asUser`).

**`kentry_tq`**: from the carried entry facts (the premises of
`kcall_tq_sys` at the entry state), every outcome of the syscall entry has
ctq5's `EX` and ctq6's `RB`.
-/
import Fl4Proofs.P3.SpecInvCqP1
import Fl4Proofs.P3.SpecInvViG6
import Fl4Proofs.P3.SpecInvCqW
import Fl4Proofs.P3.SpecInvSbE
open Classical

namespace Fl4Proofs.P3.SInvQ.P19
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.SInvQ.P17

noncomputable section

set_option maxHeartbeats 2000000

/-! ## `as_user` replaces one TCB's architecture state -/

/-- Every state predicate closed under replacing a TCB's `tcbArch` is kept by `as_user`. -/
theorem ik_arch {P : State Unit → Prop}
    (hP : ∀ σ t x a, σ.kheap t = some (.tcb x) → P σ →
      P { σ with kheap := Function.update σ.kheap t (some (.tcb { x with tcbArch := a })) })
    {α : Type} (t : ObjRef) (u : UserMonad α) : IK P (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind ?_ fun _ => ik_pure _
  intro hσ y hy
  rw [SInv.mem_setObject hy]
  exact hP σ t x _ (getTcb_kheap hx) hσ

theorem ik_arch_fip {P : State Unit → Prop}
    (hP : ∀ σ t x a, σ.kheap t = some (.tcb x) → P σ →
      P { σ with kheap := Function.update σ.kheap t (some (.tcb { x with tcbArch := a })) })
    (t : ObjRef) : IK P (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP; exact ik_arch hP _ _

/-- The current thread's TCB facts that only read fields other than `tcbArch`. -/
theorem ct_arch_all {Q : Tcb → Prop} (hQ : ∀ x a, Q x → Q { x with tcbArch := a }) (σ : State Unit) (t : ObjRef)
    (x : Tcb) (a : ArchTcb) (hx : σ.kheap t = some (.tcb x))
    (h : ∀ y, σ.kheap σ.curThread = some (.tcb y) → Q y) (y : Tcb)
    (hy : Function.update σ.kheap t (some (.tcb { x with tcbArch := a })) σ.curThread = some (.tcb y)) : Q y := by
  by_cases e : σ.curThread = t
  · rw [e, Function.update_self] at hy
    cases hy
    exact hQ x a (h x (by rw [e]; exact hx))
  · rw [Function.update_of_ne e] at hy
    exact h y hy

section A
variable {t : ObjRef}

theorem ctExit_arch : IK SInvAll.CtExit (fl4SyscallFaultIP (Z := Unit) t) := by
  refine ik_arch_fip (fun σ t x a hx h => ?_) t
  obtain ⟨y, hy, hs⟩ := h
  show ∃ y', Function.update σ.kheap t (some (.tcb { x with tcbArch := a })) σ.curThread = some (.tcb y') ∧ _
  by_cases e : σ.curThread = t
  · rw [e] at hy ⊢
    rw [hx] at hy; cases hy
    exact ⟨_, Function.update_self .., hs⟩
  · rw [Function.update_of_ne e]; exact ⟨y, hy, hs⟩

theorem act_arch : IK (fun σ : State Unit => ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (fl4SyscallFaultIP (Z := Unit) t) :=
  ik_arch_fip (fun σ t x a hx h => ct_arch_all (Q := fun y => activeSt y.tcbState) (fun _ _ h => h) σ t x a hx h) t

theorem ctSc_arch : IK SInvI.CtSc (fl4SyscallFaultIP (Z := Unit) t) :=
  ik_arch_fip (fun σ t x a hx h => ct_arch_all (Q := fun y => y.tcbSchedContext ≠ none) (fun _ _ h => h) σ t x a hx h) t

theorem ctQ_arch : IK CtQ (fl4SyscallFaultIP (Z := Unit) t) :=
  ik_arch_fip (fun _ _ _ _ _ h => h) t

theorem simple_arch : IK Simple (fl4SyscallFaultIP (Z := Unit) t) :=
  ik_arch_fip (fun _ _ _ _ _ h => h) t

theorem fld_arch (v : ObjRef × ObjRef × ObjRef) :
    IK (fun σ : State Unit => (σ.idleThread, σ.idleSc, σ.curThread) = v) (fl4SyscallFaultIP (Z := Unit) t) :=
  ik_arch_fip (fun _ _ _ _ _ h => h) t

theorem curScT_fip : IK CurScT (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP; exact cs_asUser _ _

theorem vfh_fip : IK VfhAll (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP; exact ti_asUser _ _ (fun _ _ h => h)

end A

/-! ## The shell invariant re-based -/

theorem js_rebase {I : ObjRef × ObjRef} {ct : ObjRef} {d : Prop} {N : Irq → ObjRef} {σe s : State Unit}
    (h : Js I ct d N σe s) : Js I ct d N s s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, rfl, SInvB.BR.refl _⟩

/-! ## The entry -/

set_option maxHeartbeats 8000000 in
/-- **The ready-queue bundle across the syscall entry**: from the carried
entry facts (those of `kcall_tq_sys` at the entry state), every outcome has
ctq5's `EX` and ctq6's `RB` (`hnd` SpecInvQDom's [P]; vi3's `CtSc` from EX's
`CurScT`). -/
theorem kentry_tq (hnd : numDomains = 1) (c : Syscall) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ) (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hO : SInvG.IdleOutV σ) (hI : SInvI.IdleScOutV σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, EX y.2 ∧ RB y.2 := by
  unfold fl4KernelEntrySyscall
  intro y ⟨z, hz, hy⟩
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨w, hw, hy⟩ := hy
  dsimp only at hw hy
  have hu : uV w.2 = uV σ := SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw
  have hf : (w.2.idleThread, w.2.idleSc, w.2.curThread) = (σ.idleThread, σ.idleSc, σ.curThread) :=
    fld_arch _ σ rfl w hw
  simp only [Prod.mk.injEq] at hf
  obtain ⟨fN, fS, fC⟩ := hf
  have hX' : EX w.2 :=
    ⟨⟨tq_fl4SyscallFaultIP _ σ hX.1.1 w hw, sa_fl4SyscallFaultIP _ σ hX.1.2 w hw⟩,
      ctQ_arch σ hX.2.1 w hw, simple_arch σ hX.2.2.1 w hw, curScT_fip σ hX.2.2.2 w hw⟩
  have hR' : RB w.2 := rb_fl4SyscallFaultIP _ σ hR w hw
  have h4' : T4 w.2 := q4_fl4SyscallFaultIP _ σ h4 w hw
  have hV' : SInvI.ValidIdle w.2 := by
    have h := SInvI.vi_fl4SyscallFaultIP (N := σ.idleThread) (S := σ.idleSc) (T := σ.idleThread) (b := false)
      σ.curThread σ hV w hw
    unfold SInvI.ValidIdle; rw [fN, fS]; exact h
  have hEO' : SInvB.EntryOK w.2 := SInvB.entryOK_keep hEO hu
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    (vfh_fip σ hEO.vfh w hw)
  have hCX' : SInvAll.CtExit w.2 := ctExit_arch σ hCX w hw
  have ha' := act_arch σ ha w hw
  have hIu' : Iu σ.curThread w.2 :=
    (show IK (Iu σ.curThread) (fl4SyscallFaultIP (Z := Unit) σ.curThread) by iu_auto) σ hIu w hw
  have hIL' : IL [σ.curThread] w.2 := il_fl4SyscallFaultIP _ σ hIL w hw
  have hJ' : Js I σ.curThread d Nq σ w.2 :=
    (show IK (Js I σ.curThread d Nq σ) (fl4SyscallFaultIP (Z := Unit) σ.curThread) by js_auto) σ hJ w hw
  have hE' : EF Nq w.2 := by
    refine ⟨?_, ?_, ?_, vfh_fip σ hE.2.2.2 w hw⟩
    · show P3V Nq (uV w.2); rw [hu]; exact hE.1
    · show ScKindV (uV w.2); rw [hu]; exact hE.2.1
    · show IrqOutV (fun _ => w.2.idleSc) (uV w.2); rw [hu, fS]; exact hE.2.2.1
  rw [← fC] at hIu' hIL' hJ'
  exact kcall_tq_sys hnd true c hX' hR' h4' hV' hEO' hCX' ha' hIu' hIL' (js_rebase hJ') hE'
    (by rw [fS]; exact hI2) (by rw [hu]; exact hI1)
    (by show IrqOutV (fun _ => w.2.idleThread) (uV w.2); rw [hu, fN]; exact hO)
    (by show IrqOutV (fun _ => w.2.idleSc) (uV w.2); rw [hu, fS]; exact hI) (fun _ => ctSc_of_curScT hX'.2.2.2) y hy

end

end Fl4Proofs.P3.SInvQ.P19
