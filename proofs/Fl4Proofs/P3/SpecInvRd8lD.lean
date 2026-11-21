/-
P3 (DESIGN.md §9), invariant line G1 (rd8l, KENTRY-PLAN rd8k handoff 3):
**the bundle carries `BlockedScActive`** (spec side only, outside the JAtZ
cone).

* **`bsa_restart`**: from rd8l's shell bundle `SJ` at the shell's start, BSA
  holds at every Restart state the shell's run reaches (after the lookups,
  the decode and `set_thread_state ct Restart`): the form of rd8h's
  `PerfOK σ (.invokeReply _ _)` (= rd8e's `rd_doReplyTransfer` input) at the
  perform.
* `nq_st`, **`nq_of_ev`**: `NotQ ct` from SInvAll's `EntryJEv` (ct Running /
  Restart, or idle at an interrupt).
* **`SInvCRB σ := SInvCR σ ∧ BSA σ`**, `boot_sinvCRB` (rd8e's `boot_bsa`),
  **`kentry_sinvCRB`** / **`kcall_sinvCRB`**: ctq20's `kentry_sinvCR_ofCA` /
  `kcall_sinvCR_ofCA` (rd's `CAx` at every exit by name, as there) with
  rd8l's `kentry_bsa` / `kcall_bsa`; UtInv3 / VfhAll / CnDom are SInvA's,
  `NotQ ct` from `EntryJEv`; sb2's `ScInv` and `ScLive [J]`, IdleScOutV and
  `CAx` at the entry are separate premises (not SInvCR fields), `RR` pinned.
-/
import Fl4Proofs.P3.SpecInvRd8lC
import Fl4Proofs.P3.SpecInvAllR
open Classical

namespace Fl4Proofs.P3.SInvR.B8l
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif
  Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g Fl4Proofs.P3.SInvR.B8i Fl4Proofs.P3.SInvR.B8k

noncomputable section

set_option maxHeartbeats 4000000

/-- **BSA at every Restart state of the shell's run** (rd8h's `PerfOK` Reply input). -/
theorem bsa_restart (calling don fp : Bool) (cptr : CapRef) (I : ObjRef) (σ : State Unit)
    (hJ : SJ σ.curThread I (calling = false ∧ don = true) σ) :
    ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
      (.ok a, s) ∈ ((A12b.invF σ.curThread cptr w0.1).run w0.2).1 →
      (.ok b, s') ∈ ((A12b.invE fp cptr σ.curThread w0.1 a).run s).1 →
      ∀ y ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1, BSA y.2 := by
  intro w0 hw0 a s b s' ha hb y hy
  have hJ0 := sj_getMessageInfo (C := σ.curThread) (I := I) (D := calling = false ∧ don = true) _ σ hJ w0 hw0
  have hJs := sj_invF (C := σ.curThread) (I := I) (D := calling = false ∧ don = true) _ _ _ w0.2 hJ0 _ ha
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold A12b.invE at hb
  obtain ⟨z, hz, ⟨args, ha', hd⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hb
  swap
  · cases (Prod.mk.inj he).1
  obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz
  simp only [Except.ok.injEq] at ha'; subst ha'
  have hJx := sj_getMrs (C := σ.curThread) (I := I) (D := calling = false ∧ don = true) _ _ _ s hJs x hx
  have hJs' : SJ σ.curThread I (calling = false ∧ don = true) s' :=
    (sje_of (by ba_auto) (fun _ => by sb_auto) (fun _ => by uk_auto) (fun _ => by isk_auto)
      (ws_of_kz fun V => A12b.kz_fl4DecodeInvocation (V := V) _ _ _ _ _ _ _ _) (by vfc_auto)) x.2 hJx _ hd
  exact (sj_setThreadState (C := σ.curThread) (I := I) (D := calling = false ∧ don = true)
    σ.curThread .restart rfl s' hJs' y hy).1.1

theorem nq_st {ev : Event} {st : ThreadState}
    (h : SInv.activeSt st ∨ (ev = .interrupt ∧ st = .idleThreadState)) : ipcQueuedThreadState st = false := by
  rcases h with h | ⟨-, h⟩
  · cases st <;> first | rfl | exact h.elim
  · subst h; rfl

/-- `NotQ ct` from SInvAll's per-event entry fact. -/
theorem nq_of_ev {ev : Event} {σ : State Unit} (h : SInvAll.EntryJEv ev σ) : NotQ σ.curThread σ := by
  obtain ⟨x, hx, ha⟩ := h.ctAct
  intro x' hx'
  rw [hx] at hx'; cases hx'
  exact nq_st ha

/-! ## The bundle -/

/-- **ctq20's `SInvCR` with `BlockedScActive`.** -/
abbrev SInvCRB (σ : State Unit) : Prop := SInvAll.SInvCR σ ∧ BSA σ

/-- **`SInvCRB` at boot** (non-vacuity). -/
theorem boot_sinvCRB : SInvCRB (initASt (Z := Unit)) := ⟨SInvAll.boot_sinvCR, B8e.boot_bsa⟩

/-- **`SInvCRB` across the syscall entry.** Premises: ctq20's (`hnd` [P], ct ≠
idle, rd's `CAx` at every exit by name), and for BSA: sb2's `ScInv` and
`ScLive` [J], IdleScOutV, `CAx` at the entry; `RR` pinned to the run. -/
theorem kentry_sinvCRB (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvCRB σ)
    (hct : σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvR.CAx r.2)
    (hI : SInvB.ScInv σ) (hL : SInvB.ScLive σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hA : SInvR.CAx σ)
    (hR : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, ∀ z ∈ (updateTimeStamp (Z := Unit) w.2).1,
      RR true z.2 c) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvCRB y.2 := by
  have hA' := h.1.1.1.1.1
  have hNQ : NotQ σ.curThread σ := nq_of_ev (ev := .syscallEvent c) (SInvAll.SInvB.entryJEv h.1.1.1 fun _ => hct)
  exact fun y hy => ⟨SInvAll.kentry_sinvCR_ofCA hnd c h.1 hct hCA y hy,
    kentry_bsa c h.2 ⟨hI, hA'.ut, hA'.vfh, hL⟩ hO hA'.cnDom hA hNQ hct hR y hy⟩

/-- **`SInvCRB` across every kernel event** (premises as `kentry_sinvCRB`, ct ≠
idle for a non-interrupt event). -/
theorem kcall_sinvCRB (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvCRB σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvR.CAx r.2)
    (hI : SInvB.ScInv σ) (hL : SInvB.ScLive σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hA : SInvR.CAx σ)
    (hR : ∀ c, ev = .syscallEvent c → ∀ z ∈ (updateTimeStamp (Z := Unit) σ).1, RR rep z.2 c) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvCRB y.2 := by
  have hA' := h.1.1.1.1.1
  have hNQ : NotQ σ.curThread σ := nq_of_ev (SInvAll.SInvB.entryJEv h.1.1.1 hev)
  exact fun y hy => ⟨SInvAll.kcall_sinvCR_ofCA hnd rep ev h.1 hev hCA y hy,
    kcall_bsa rep ev h.2 ⟨hI, hA'.ut, hA'.vfh, hL⟩ hO hA'.cnDom hA hNQ hev hR y hy⟩

end

end Fl4Proofs.P3.SInvR.B8l
