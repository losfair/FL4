/-
P3 (DESIGN.md §9), TCB: **the FPU release at `J`** (`JAtZ.fpuReleaseJ`;
the last step of a final thread cap's finalisation, XTopJointFinThread's
`JAtZ.finThreadJ`, in place of a whole-step premise).

FL4's `fpu_release` (the extracted `finalise_cap_object`, Thread case:
`machineArchInst.fpu_release a4 ptr`) changes only the arch state `A`: the
store is not touched (the eager FPU switching and the remote FPU flush of
the arch backend live behind `machine.Arch`). The spec's `fpu_release`
(l4v `FPU_A.fpu_release`) changes, when the thread owns the FPU, the
thread's saved FPU image and `tcbCurFpu` (its registers kept), the current
FPU owner and the machine state (not the user memory); else nothing. No
relation of `JAtZ` reads those, so:

Spec outcome, `IRel` and `XTopAt` steps in XTopFpuRel:

* `fpuRelease_outF`: an outcome of the spec's `fpu_release` of a TCB, in the
  normal form `{updK σ t (.tcb {x with tcbArch := ta}) with machineState :=
  ms, archState := {σ.archState with x64CurrentFpuOwner := o}}`, the
  registers (`ta`) and the user memory (`ms`) kept.
* `Ipc.irel_tcbArch`: `IRel` across a spec-only change of a TCB's
  `tcbArch` keeping its registers (`reg_wr_irel` without FL4's write).
* `JAtZ.tcbArchJ`: `JAtZ` across that change (XTopJointRegFrame's
  `JAtZ.reg_frame`, FL4's store kept: a quiet step `QKY`, an `ArchStep`).
* `JAtZ.arFrS`: `JAtZ` across a spec step in XTopJointFinVsSpec's frame
  `ArFr` with FL4's store kept and any arch state related by `XTopAt` after
  (as XTopJointFinVs's `finVsJb` with no word written).
* `XTopAt.fpuOwner`: `XTopAt` across the FPU owner's and the machine
  state's change (`XTopAt.frameStep`, the user memory kept), at an arch
  state related to the same CR3.
* `JAtZ.fpuReleaseJ`: FL4's `fpu_release` against the spec's at `J`, from
  `ARKeep.fpu_release` [P] (part of `ARIface`, already a top-level premise:
  `JDelParts.arKeep`).
-/
import Fl4Proofs.P3.XTopJointFinVs
import Fl4Proofs.P3.XTopJointYield
import Fl4Proofs.P3.XTopFpuRel
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

/-! ## `JAtZ` across the FPU release -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a spec-only change of a TCB's arch part keeping its
registers** (`JAtZ.reg_frame` with FL4's store kept). -/
theorem JAtZ.tcbArchJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (ta : Fl4Spec.ArchTcb)
    (hr : ta.tcbContext.userRegs = x.tcbArch.tcbContext.userRegs) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s a (updK σ t.bv (.tcb { x with tcbArch := ta })) := by
  have hI := J.xtop.irelK J.ks J.buf
  have hI3 := irel_tcbArch J.ip hI ht hk ta hr
  have hAS : ArchStep σ (updK σ t.bv (.tcb { x with tcbArch := ta })) := archStep_updTcb hk rfl
  have hA : QKY σ (updK σ t.bv (.tcb { x with tcbArch := ta })) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
    by_cases e : q = t.bv
    · subst e; exact Or.inr (Or.inl ⟨x, { x with tcbArch := ta }, hk, by simp [updK], rfl⟩)
    · exact Or.inl (by simp [updK, e])
  exact J.reg_frame hI3 (P1.WritesIn.refl s _) hA hAS.ykeep (hAS.inv J.inv) J.blk (P1.WritesIn.refl s _)

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across an `ArFr` spec step with FL4's store kept** (XTopJointFinVs's
`finVsJb` with no word written): `XTopAt` after given (at any arch state). -/
theorem JAtZ.arFrS (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {a' : A} {σ' : Fl4Spec.State Unit}
    (F : ArFr σ σ') (hX : XTopAt (L := L) AR Z s a' σ') :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a' σ' := by
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s) := SlotsSame.refl _ _
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have k1 : ∀ t ∈ Z.T, L.mem s (mcpA t) = L.mem s (mcpA t) := fun _ _ => rfl
  have k2 : ∀ t ∈ Z.T, L.mem s (P1.yieldA t) = L.mem s (P1.yieldA t) := fun _ _ => rfl
  have kb : ∀ t ∈ Z.T, L.mem s (tIpcBufA t) = L.mem s (tIpcBufA t) := fun _ _ => rfl
  have k3 : ∀ q ∈ Z.C, L.mem s (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun _ _ => rfl
  have k4 : ∀ r ∈ Z.R, L.mem s (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s (P1.rNextA r) = L.mem s (P1.rNextA r) := fun _ _ => ⟨rfl, rfl⟩
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (F.look (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩,
    fun p x n hp => ⟨x, F.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, F.sc.1 hp, rfl⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ rfl ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s σ' :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) rfl (fun _ _ => rfl) rfl⟩
  have hkern := J.kern_keepA rfl rfl hX.fin.1.1.1 F rfl
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s σ' Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap hdv
    have U := J.utc sl p sb fi dev hsl hcap hdv
    refine ⟨U.pal, U.pfit, U.fiLe, U.high, U.actZ, U.free, U.zero, U.sb4, U.nostr, U.nsFree,
      fun h0 => U.ns (by rw [F.cdt] at h0; exact h0), ?_, U.dwReg, fun g => by rw [F.gpml4]; exact U.gReg g⟩
    intro g h0 hf0
    rw [F.cdt] at h0
    obtain ⟨r1, r3⟩ := U.rst g h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← F.orig]; exact h), r3⟩
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩),
      J.buf.frame kb (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩), hRP',
      J.apart.sc_frame rfl F.szKeep, hjpl, J.jcov, hkern, hutc, J.nsc.ar F, J.inv.ar F, CurInvW.ar J.cur F,
      J.own.ar F, J.off.ar F, J.act.ar F, J.bsa.ar F, J.isorted.ar F, J.curRun.ar F, J.blk⟩
  exact J.cs_frameK rfl hX F.kback F.ipcFr (JCs.same J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) VKeep.rfl'
    hSS (P1.DbgKeep.refl s) F.idle

/-- The FPU owner's and the machine state's change is an `ArFr` step. -/
theorem arFr_fpuOwner (σ : Fl4Spec.State Unit) (ms : Fl4Spec.MachineState) (o : Option Fl4Spec.ObjRef) :
    ArFr σ { σ with machineState := ms, archState := { σ.archState with x64CurrentFpuOwner := o } } :=
  ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **FL4's `fpu_release` at `J`** (module docstring): against an outcome of
the spec's, `JAtZ` after at FL4's new arch state, from `ARKeep` [P]. -/
theorem JAtZ.fpuReleaseJ (hK : ARKeep arI AR) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64}
    (ht : t ∈ Z.T) :
    arI.fpu_release a t ⦃ a' => ∃ σ', ((), σ') ∈ (Fl4Spec.fpuRelease (Z := Unit) t.bv σ).1 ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s a' σ' ⦄ := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_mono (hK.fpu_release a t _ hAR) ?_
  intro a' hAR'
  obtain ⟨Q, R0, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  obtain ⟨ta, ms, o, hr, hum, hm⟩ := Sched.fpuRelease_outF hk
  obtain ⟨V1, J1⟩ := J.tcbArchJ ht hk ta hr
  exact ⟨_, hm, V1, J1.arFrS (arFr_fpuOwner _ ms o) (J1.xtop.fpuOwner ms o hum hAR')⟩

end

end

end Fl4Proofs.P3
