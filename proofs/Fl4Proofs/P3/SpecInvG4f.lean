/-
P3 (DESIGN.md §9), invariant line G4 (g4f, KENTRY-PLAN g4f item (1)):
**the carried spec bundle across the FaultIP write** (spec side only, outside
the JAtZ cone).

* `sinvWR_fip`: `SInvW σ ∧ RPos σ` (XTopJointKEntry35's `SInvX`) holds at
  every outcome of `fl4SyscallFaultIP t` (one `asUser` register write of `t`),
  for any `t`. Every field from its family's `fl4SyscallFaultIP` kit (the
  cap view `uV`, the IRQ node, the idle pair, the binding frame `BR`, the
  per-family `IK` leaves), or by `ik_arch_fip` (the field reads no `tcbArch`:
  `RS`, `OffReady`, `CAx`).
-/
import Fl4Proofs.P3.SpecInvRd14hC
import Fl4Proofs.P3.SpecInvEqS
open Classical

namespace Fl4Proofs.P3.SInvR.G4f
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvR.B8w

noncomputable section

variable {t : ObjRef}

/-- The idle pair and the current thread across the write. -/
theorem fld_fip {σ : State Unit} {w : Unit × State Unit} (hw : w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1) :
    w.2.idleThread = σ.idleThread ∧ w.2.idleSc = σ.idleSc ∧ w.2.curThread = σ.curThread := by
  have h := SInvQ.P19.fld_arch (t := t) (σ.idleThread, σ.idleSc, σ.curThread) σ rfl w hw
  simp only [Prod.mk.injEq] at h
  exact h

theorem rs_fip : SInv.IK SInvQ.RS (fl4SyscallFaultIP (Z := Unit) t) :=
  SInvQ.P19.ik_arch_fip (fun _ _ _ _ _ h => h) t

theorem offReady_fip : SInv.IK Sched.OffReady (fl4SyscallFaultIP (Z := Unit) t) := by
  refine SInvQ.P19.ik_arch_fip (fun σ t x a hx h => ?_) t
  intro y n hy
  change Function.update σ.kheap t (some (.tcb { x with tcbArch := a })) σ.curSc = some (.schedContext y n) at hy
  by_cases e : σ.curSc = t
  · exfalso
    rw [e, Function.update_self] at hy; cases hy
  · rw [Function.update_of_ne e] at hy
    exact h y n hy

theorem cAx_fip : SInv.IK SInvR.CAx (fl4SyscallFaultIP (Z := Unit) t) := by
  refine SInvQ.P19.ik_arch_fip (fun σ t x a hx h => ?_) t
  intro hne
  obtain ⟨x0, c, y, n, h1, h2, h3, h4⟩ := h hne
  have hct : c ≠ t := fun e => by rw [e, hx] at h3; cases h3
  have h3' : Function.update σ.kheap t (some (.tcb { x with tcbArch := a })) c = some (.schedContext y n) := by
    rw [Function.update_of_ne hct]; exact h3
  by_cases e : σ.curThread = t
  · rw [e, hx] at h1; cases h1
    refine ⟨{ x with tcbArch := a }, c, y, n, ?_, h2, h3', h4⟩
    show Function.update σ.kheap t _ σ.curThread = _
    rw [e, Function.update_self]
  · exact ⟨x0, c, y, n, by show Function.update σ.kheap t _ σ.curThread = _; rw [Function.update_of_ne e]; exact h1,
      h2, h3', h4⟩

set_option maxHeartbeats 4000000 in
/-- **`SInvX` across the FaultIP write** (module docstring). -/
theorem sinvWR_fip {σ : State Unit} (h : SInvW σ ∧ SInvE.RPos σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1, SInvW w.2 ∧ SInvE.RPos w.2 := by
  intro w hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hA, hCE⟩, hOI⟩, ⟨⟨hTQ, hSA⟩, hCQ, hSi, hCS⟩, hRB, hT4⟩, hRS⟩, hBSA⟩, hVB⟩, hRd, hOR, hCA⟩, hRP⟩ := h
  obtain ⟨hid, hisc, -⟩ := fld_fip hw
  have hU : SInvU.uV w.2 = SInvU.uV σ := SInvU.uk_fl4SyscallFaultIP t σ rfl w hw
  have hN : w.2.interruptIrqNode = σ.interruptIrqNode := SInvU.nk_fl4SyscallFaultIP t σ rfl w hw
  have hcap : SInvU.capAt w.2 = SInvU.capAt σ := congrArg (fun v => v.2.1) hU
  have hvc := (show SInv.IK SInv.VfC (fl4SyscallFaultIP (Z := Unit) t) by vfc_auto) σ
    ⟨(SInv.vfhV_iff σ).2 hA.vfh, hA.cnDom⟩ w hw
  have hb := (SInv.b_of_gf (fun _ _ => SInv.fg_fl4SyscallFaultIP t) :
    SInv.BK [] [] [] (fun _ => True) (fl4SyscallFaultIP (Z := Unit) t)) σ
    ((SInv.b_nil_iff σ).2 ⟨hA.fts, hA.nqb⟩) w hw
  have hb' := (SInv.b_nil_iff _).1 hb
  have hv := SInvV.hv_fl4SyscallFaultIP (P := SInvV.VI) t σ ⟨hA.vim, hA.vih, trivial⟩ w hw
  have hq := (SInv.nq_nil_iff _).1 (SInv.nq_fl4SyscallFaultIP (Kq := []) t σ
    ((SInv.nq_nil_iff σ).2 ⟨hA.nq, hA.epq⟩) w hw)
  have hl := (SInv.il_nil_iff _).1 (SInv.il_fl4SyscallFaultIP (Kq := []) t σ ((SInv.il_nil_iff σ).2 hA.live) w hw)
  have hvi := SInvI.vi_fl4SyscallFaultIP (N := σ.idleThread) (S := σ.idleSc) (T := σ.idleThread) (b := false) t σ
    hA.vi w hw
  have hoi := SInvF.oi_fl4SyscallFaultIP (Qo := σ.archState.x64CurrentFpuOwner) t σ
    ⟨rfl, fun o ho => (hA.ft o ho).1⟩ w hw
  have hsl := hA.sl
  have hsc := (SInvL.sl_nil_iff _).1 (SInvL.sl_fl4SyscallFaultIP (Iq := SInvL.idleP σ) (Kq := []) t σ
    ((SInvL.sl_nil_iff σ).2 hsl.1.1) w hw)
  have hA' : SInvAll.SInvA w.2 := {
    vfh := (SInv.vfhV_iff _).1 hvc.1
    cnDom := hvc.2
    fts := hb'.1
    nqb := hb'.2
    ns := SInv.ns_fl4SyscallFaultIP t σ hA.ns w hw
    sg := ⟨fun irq a h' => hA.sg.irq irq a (by rw [hN] at h'; rwa [hcap] at h'),
      fun p cref a h' hf irq => by rw [hN]; exact hA.sg.ref p cref a (by rwa [hcap] at h') hf irq,
      fun p cref a h' hf => by rw [hid]; exact hA.sg.idle p cref a (by rwa [hcap] at h') hf⟩
    idleOut := by unfold SInvG.IdleOutV; rw [hU, hid]; exact hA.idleOut
    dom := SInvDom.dp_of_dl (SInvDom.dl_fl4SyscallFaultIP t) σ w hA.dom hw
    vim := hv.1
    vih := hv.2.1
    vmt := SInvV.gk_fl4SyscallFaultIP t _ SInvV.wl_vmt σ hA.vmt w hw
    ut := by
      have h0 := hA.ut
      refine (show SInvU.UtInv''V (SInvU.uV w.2) ∧ SInvU.IrqOutV w.2.interruptIrqNode (SInvU.uV w.2) from ?_)
      rw [hU, hN]; exact h0
    nq := hq.1
    epq := hq.2
    live := hl
    vi := by unfold SInvI.ValidIdle; rw [hid, hisc]; exact hvi
    ft := fun o ho => ⟨hoi.2 o (hoi.1.symm.trans ho),
      let ⟨s, hs⟩ := (hA.ft o (hoi.1.symm.trans ho)).2; ⟨s, by rw [hcap]; exact hs⟩⟩
    sl := ⟨⟨by show SInvL.ScLiveT (w.2.idleThread, w.2.idleSc) w.2; rw [hid, hisc]; exact hsc,
        by unfold SInvL.IdleScOutV; rw [hU, hisc]; exact hsl.1.2.1,
        SInvL.nb_fl4SyscallFaultIP t σ hsl.1.2.2.1 w hw,
        SInvB.scInv_of_br hsl.1.2.2.2 (SInvB.sb_fl4SyscallFaultIP (h0 := σ.kheap) t σ (SInvB.BR.refl _) w hw)⟩,
      by show SInvL.ScKindRV (SInvU.uV w.2); rw [hU]; exact hsl.2⟩
    cs := SInvQ.P19.curScT_fip σ hA.cs w hw }
  have hOI' : SInvAll.OnlyIdle w.2 := by
    have h0 := SInvAll.oi_fl4SyscallFaultIP (N := σ.idleThread) t σ hOI w hw
    intro t' x hx hs; rw [hid]; exact h0 t' x hx hs
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hA', SInvQ.P19.ctExit_arch σ hCE w hw⟩, hOI'⟩,
    ⟨⟨SInvQ.tq_fl4SyscallFaultIP t σ hTQ w hw, SInvQ.sa_fl4SyscallFaultIP t σ hSA w hw⟩,
      SInvQ.P19.ctQ_arch σ hCQ w hw, SInvQ.P19.simple_arch σ hSi w hw, SInvQ.P19.curScT_fip σ hCS w hw⟩,
    SInvQ.rb_fl4SyscallFaultIP (k := true) t σ hRB w hw, SInvQ.q4_fl4SyscallFaultIP t σ hT4 w hw⟩,
    rs_fip σ hRS w hw⟩, SInvR.B8g.ba_fl4SyscallFaultIP t σ hBSA w hw⟩, ?_⟩,
    SInvR.rd_fl4SyscallFaultIP t σ hRd w hw, offReady_fip σ hOR w hw, cAx_fip σ hCA w hw⟩,
    SInvE.pz_fl4SyscallFaultIP t σ hRP w hw⟩
  intro t' hs hne hsw
  exact SInvR.B8q.ve_fl4SyscallFaultIP (E := fun _ => False) t σ (fun t'' _ => hVB t'') w hw t' not_false hs hne hsw

end

end Fl4Proofs.P3.SInvR.G4f
