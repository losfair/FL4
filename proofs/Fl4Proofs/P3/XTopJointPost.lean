/-
P3 (DESIGN.md §9), CSpace: **a cleanup cap's `post_cap_deletion` at `J`**
(`JPostDelHyp`, XTopJointDelR, discharged: `jPostDelHyp_of`). The IRQ
handler's and the IO port's cleanups are kernel-state steps (XTopPostDel's
`post_irqX`, `post_ioX`: FL4 writes `KsW` words only, the spec's step is
`KsStep`), so `JAtZ` after by `jowes_ks` and `cs_frame`, as StepSem's
kernel-state steps (`stepClosed_jat`).
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.XTopPostDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`JPostDelHyp` holds** (module docstring): the kernel-state block's
layout from the state's `JAtZ` (`JAtZ.intL`, `JAtZ.ioLay`), the arch IRQ
operations total and keeping `AR` (`ARMask` [P]), as `xPostDelHyp_of`. -/
theorem jPostDelHyp_of {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {th : TypedHeap}
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a') :
    JPostDelHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G cl _ ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩ hcl hcln hclw
  subst hth
  have hX := J.xtop
  have hLy : IntLayout Z.th (L.ksb s) ∧ IoLayout Z.th (L.ksb s) := ⟨J.intL, J.ioLay⟩
  have hfin : ∀ (s' : S) (a' : A) (σ' : Fl4Spec.State Unit), SlotsSame (Z.mv G V).th (L.mem s) (L.mem s') →
      P1.WritesIn st s s' (KsW (L.ksb s)) → KsStep σ σ' → XTopAt (L := L) AR (Z.mv G V) s' a' σ' →
      WJR (L := L) arI AR Z H Cs kb s' a' σ' G := fun s' a' σ' hSS hw hO hX' => by
    obtain ⟨Ac', Lst', R⟩ := jowes_ksD arI s s' a a' σ σ' hw hO _ H Cs Ac Lst D rfl J hX'
    exact ⟨V, Ac', Lst', D, J.cs_frameK hw.1 hX' (KBack.of_kheap hO.kh) (IpcFrKeep.of_kheap hO.kh) (JCs.same J hSS (KSz.of_kheap hO.kh)) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J.vkeep_of hw fun _ hb => J.ksW_nv hb)
      hSS (dbgKeep_of_writes J.blk hw fun _ hb => J.ksW_notDbg hb) hO.idle,
      by rw [hw.1]; exact hkb, fun u e => hns u (by rw [← hO.act]; exact e), hsg.of_eq hO.kh hO.inode hO.idle, hp0.of_ppk (PPK.of_ksStep hO)⟩
  cases cl <;> simp only [CleanCap] at hcl
  · exact absurd rfl hcln
  · refine WP.spec_mono (post_irqX arI hAM hX J.ks (hLy.1) hmask hfree _ hclw) ?_
    rintro r ⟨hSS, -, σ', hm, hCR, hw, hO, hX'⟩
    exact ⟨hSS, σ', hm, hCR, hfin _ _ _ hSS hw hO hX'⟩
  · obtain ⟨hf, hl, hfl⟩ := hclw
    refine WP.spec_mono (post_ioX arI hX J.ks (hLy.2) _ _ _ hfl hl) ?_
    rintro r ⟨hSS, -, σ', hm, hCR, hw, hO, hX'⟩
    exact ⟨hSS, σ', hm, hCR, hfin _ _ _ hSS hw hO hX'⟩

end

end

end Fl4Proofs.P3
