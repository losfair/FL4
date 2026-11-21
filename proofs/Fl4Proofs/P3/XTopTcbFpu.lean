/-
P3 (DESIGN.md §9), CSpace and TCB: **ReadFPU and WriteFPU at `XTop`**
(`tcb_fpuX`).

* `XTopAt.tcbWrF`: a write of a TCB's FPU-image word (offsets 512..3208,
  read by no relation), as `XTopAt.tcbWrA`.
* `XTopAt.arch`: `XTopAt` at another arch state related to the same CR3.
* `copy_words_inv`: FL4's `copy_words` keeps an invariant kept by each of
  its destination writes.
* `fpu_refinesX`: `fpu_refines` (TcbExt) at `X`: the checks proved, the work
  (`FpuHypX`).
* `fpuHypX_write`: WriteFPU's work at `XTop`: the restart, `fpu_flush`, the
  frame's words copied into the TCB's FPU image (`XTopAt.tcbWrF`), then
  `fpu_sanitise`, `fpu_reload` (the arch relation kept: `ARIface` [P]).
* `fpuHypX_read`: ReadFPU's work at `XTop`, from the user-frame write
  (`FpuFrameXHyp` [W]): the spec's step (`Fl4Spec.fl4FpuToFrame`) changes
  only the user memory, inside the frame's 2696 bytes, so the
  obligation is `XTopAt` after FL4's writes of the frame's words at a state
  whose user memory agrees with the old one outside those bytes
  (`fpuToFrame_mem`, `fpu_store_other`).
-/
import Fl4Proofs.P3.XTopTcbBp
import Fl4Proofs.P3.XTopReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Ipc Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 4000000 in
/-- **A TCB's FPU-image word written** (offsets 512..3208: read by no
relation; the proof is `XTopAt.tcbWrA`'s). -/
theorem XTopAt.tcbWrF {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {t : U64} (ht : t ∈ Z.T) (wa : U64) (Kv : Nat)
    (hKw : 512 ≤ Kv ∧ Kv < 3208 ∧ Kv % 8 = 0) (hwav : wa.val = t.val + Kv)
    (v : U64) :
    XTopAt (L := L) AR Z (L.wr s (wa) v) a σ := by
  have hSch := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  have hT := hc.tcbs
  have hta := hT t ht
  have hP := hX.fin.1.2
  have hPe := hP.ep
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko := hc.ksOut t ht
  have hwv : wa.val = t.val + Kv := hwav
  have hwa : P1.Aligned (wa) := by unfold P1.Aligned; rw [hwv]; have := hta.align; omega
  have hw : P1.WritesIn st s (L.wr s (wa) v) (· = wa) := P1.writesIn_wr hwa
  have hne : ∀ b : U64, P1.Aligned b → b.val ≠ t.val + Kv →
      L.mem (L.wr s (wa) v) b = L.mem s b := fun b hb hbv =>
    hw.mem_eq hb fun e => hbv (by rw [e, hwv])
  -- the scheduler relation
  have hN := hc.node
  have hnd := hN.disj t ht
  have hSA : Sched.SAgree st Z.T Z.C Z.c s (L.wr s (wa) v) := by
    refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ _ _ _ => hne _ (P1.nodeAt_aligned hN ho h8) ?_, fun y hy K hK => ?_,
      hne _ ?_ ?_, hne _ ?_ ?_, fun sc hsc b hb hin => hne _ hb ?_⟩
    · rw [P1.nodeAt_val hN ho]; omega
    · obtain ⟨h1, h2, -⟩ := Sched.schedField_ok hK
      refine hne _ (P1.field_aligned (hT y hy) h1 h2) ?_
      rw [Notif.tfield_val (hT y hy) h1]
      by_cases e : y = t
      · subst e; rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
      · have := tcb_disj hPe ht hy e; omega
    · unfold Sched.curDomA; unfold P1.Aligned
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.curDomA
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.dtA; unfold P1.Aligned
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.dtA
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · have := (hSch.scOutIn hsc hin).2.2.1 t ht; omega
  have hSch' : Sched.SchedRel st Z.N Z.T Z.C Z.c (L.wr s (wa) v) σ := by
    refine hSch.of_sagree hSA ?_ ?_ ⟨rfl, rfl, fun _ => Or.inl rfl⟩
    · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
      exact hne _ (P1.nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
        (by rw [P1.nodeAt_val hN (by simp [layout.node.SCHED_ACTION])]; simp only [layout.node.SCHED_ACTION]; simp; omega)
    · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
      exact hne _ (P1.nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
        (by rw [P1.nodeAt_val hN (by simp [layout.node.REPROGRAM])]; simp only [layout.node.REPROGRAM]; simp; omega)
  refine hX.frameStep hw (fun b hb => by subst hb; exact Or.inr (Or.inr (Or.inl ⟨t, ht, by omega, by omega⟩)))
    (fun b hb hf => ?_) (fun b hb hf => ?_) (fun hb => ?_) rfl rfl rfl rfl rfl rfl rfl hSch' ?_ ?_ ?_
    hX.fin.1.1.2.2.2.2.2.2
  · -- not read by the endpoint relation
    subst hb
    rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨y, hy, h | h⟩ | ⟨wp, hwp, h⟩
    · have := hPe.et e he t ht; omega
    · have := hPe.rt r hr t ht; omega
    · obtain ⟨h1, h2⟩ := h
      unfold Endp.TOffN at h2
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
    · unfold Endp.TL at h
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
    · have := hPe.bt wp hwp t ht; rw [← h] at this; omega
  · -- not read by the notification relation
    subst hb
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨y, hy, h⟩
    · have := hSch.placed.disj n hn t ht; omega
    · have hv := nfootT_val (hT y hy) h
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
  · -- not the kernel root
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have := congrArg UScalar.val hb
    rw [hkv, hwv] at this; omega
  · -- the IRQ relation
    have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)]
    exact hI.st i hi
  · -- the IO-port relation
    have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)]
    exact hI p hp
  · -- the domain schedule
    refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)

set_option maxHeartbeats 4000000 in
/-- **`XTopAt.frameStep` with the written words outside the VSpace objects**
(in place of "among the other objects": the user words). -/
theorem XTopAt.frameStepV {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hWV : ∀ b, W b → ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b)
    (hWE : ∀ b, W b → ¬ Endp.EFoot Z.T Z.E Z.R Z.B b) (hWN : ∀ b, W b → ¬ Notif.NFoot Z.N Z.T b)
    (hWK : ¬ W (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT))
    (hkh : σ'.kheap = σ.kheap) (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hct : σ'.curThread = σ.curThread)
    (hum : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory)
    (hasid : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hSch' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ')
    (hIrq' : IrqRel (L.mem s') (L.ksb s) σ') (hIo' : IoRel (L.mem s') (L.ksb s) σ')
    (hD' : DomRel (L.mem s') (L.ksb s) σ') (hAR' : AR a' σ'.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s' a' σ' := by
  obtain ⟨⟨⟨⟨hSch, hEp, hNt, -, -, hKr, -⟩, hP⟩, hR, hPt, hPI, hCO⟩, ⟨hPl, hCR, hFI, -, hMO, hIA, hSA⟩, -, hE⟩ := hX
  have hk : L.ksb s' = L.ksb s := hw.1
  have hvobj : ∀ b, VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b → ¬ W b :=
    fun b hv hb => hWV b hb hv
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    slotsSame_of_vobj hPl fun b hb hv => hw.mem_eq hb (hvobj b hv)
  have hEp' : Endp.EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' :=
    Endp.EpStateRel.frame hEp hP.ep (fun b hb hf => hw.mem_eq hb fun h => hWE b h hf)
      ⟨fun p x h => by rw [hkh]; exact h, fun p x h => ⟨x, by rw [hkh]; exact h, rfl⟩,
        fun p x h => ⟨x, by rw [hkh]; exact h, rfl, rfl, rfl, rfl, rfl⟩, hum⟩
  have hNt' : Notif.NtfnStateRel Z.N Z.T (L.mem s') σ' :=
    Notif.NtfnStateRel.frame hNt hSch.placed (fun b hb hf => hw.mem_eq hb fun h => hWN b h hf)
      ⟨fun p x h => by rw [hkh]; exact h, fun p x h => ⟨x, by rw [hkh]; exact h, rfl, rfl, rfl⟩⟩
  have hKr' : KRootRel (L.mem s') (L.ksb s') σ' := by
    unfold KRootRel globCr3 at hKr ⊢
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    have hka := hP.vs.ksb_al
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hk, hw.mem_eq (by unfold P1.Aligned; rw [hkv]; omega) hWK, hgp]
    exact hKr
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hw.mem_eq (VsWrite.aligned hP.vs hb) (hvobj b (vsWrite_vobj hP.vs hb))
  have hSz : Sched.SzKeep σ σ' := Sched.SzKeep.of_kheap hkh
  refine ⟨⟨⟨⟨hSch', hEp', hNt', by rw [hk]; exact hIrq', by rw [hk]; exact hIo', hKr', hAR'⟩, ?_⟩, ?_, ?_,
    fun q hq lo hl => ?_, hCO.of_same hSS hct⟩,
    ⟨hPl, crel_same hCR hSS hkh hcdt horig, hFI.of_same hCR.2.2.1 hSS (KSub.of_kheap hkh),
      by rw [hk]; exact hD', by rw [hk]; exact MdbOKV.of_same hCR.2.2.1 hSS hMO, by rw [hk]; exact hIA,
      hSA.mono hSz⟩, IpcRel.of hNt' hEp' (sched_sc hSch'), hE.mono hk hSz⟩
  · refine ⟨hP.ep, by rw [hk]; exact hP.vs, hP.pt, hP.pl, fun x hx => by
      rw [hk]; exact hP.disj x (OObj.of_same hk hkh hx), fun x h1 h2 => ?_,
      hP.po, hP.ps, by rw [hk]; exact hP.pv, by rw [hk]; exact hP.vo, by rw [hk]; exact hP.sd, by rw [hk]; exact hP.tko⟩
    have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp [P1.LawfulStore.nodeBase, hk]
    rw [hnb] at h1 h2; exact hP.nodeE x h1 h2
  · rw [hk]
    refine hR.frame hvw hasid fun p hp => ?_
    rw [hkh]
  · refine hPt.frame (fun b ⟨q, hq, i, hi, e⟩ => ?_) fun q hq => by rw [hkh]
    subst e
    have hv := table_vobj (th := Z.th) (P := Z.P) hP.pt hq hi (L.ksb s)
    exact hw.mem_eq (hP.po _ ⟨q, hq, i, hi, rfl⟩).1 (hvobj _ hv)
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl

/-- **A user word** (ReadFPU's frame words) [J]: aligned, apart from the
kernel-global area, the node, the TCBs and the SCs (`Far`), from the VSpace
objects (and so the slots), the endpoints, the replies and the
notifications (l4v `valid_cap` of a frame cap with `pspace_distinct`). -/
structure UserW (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) (b : U64) : Prop where
  al : P1.Aligned b
  far : Sched.Far st Z.T Z.C Z.c s σ b
  vobj : ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b
  ep : ∀ e ∈ Z.E, b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val
  rep : ∀ r ∈ Z.R, b.val + 8 ≤ r.val ∨ r.val + 32 ≤ b.val
  ntfn : ∀ n ∈ Z.N, b.val + 8 ≤ n.val ∨ n.val + 64 ≤ b.val

set_option maxHeartbeats 4000000 in
/-- **A user word not an IPC-buffer word, written**, keeps `XTopAt` (the
spec's state kept). -/
theorem XTopAt.userWr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {b : U64} (hu : UserW (L := L) Z s σ b) (hnB : ∀ wp ∈ Z.B, wp.1 ≠ b)
    (v : U64) : XTopAt (L := L) AR Z (L.wr s b v) a σ := by
  have hSch := hX.fin.1.1.1
  have hP := hX.fin.1.2
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hT := hc.tcbs
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  obtain ⟨hf1, hf2, -⟩ := hu.far
  have hw : P1.WritesIn st s (L.wr s b v) (· = b) := P1.writesIn_wr hu.al
  have hne : ∀ x : U64, P1.Aligned x → x.val ≠ b.val → L.mem (L.wr s b v) x = L.mem s x :=
    fun x hx h => hw.mem_eq hx fun e => h (by rw [e])
  have hbal : b.val % 8 = 0 := hu.al
  refine hX.frameStepV hw (fun x hx => by subst hx; exact hu.vobj) (fun x hx hf => ?_) (fun x hx hf => ?_)
    (fun hx => ?_) rfl rfl rfl rfl rfl rfl rfl (hSch.wr_far hu.al hu.far v) ?_ ?_ ?_ hX.fin.1.1.2.2.2.2.2.2
  · subst hx
    rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hwp, h⟩
    · have := hu.ep e he; have := (hP.ep.ep e he).1; omega
    · have := hu.rep r hr; have := (hP.ep.rep r hr).1; omega
    · have := hf2 t ht; have := h.range; have := (hT t ht).align; omega
    · have := hf2 t ht; unfold Endp.TL at h; have := (hT t ht).align; omega
    · exact hnB wp hwp h.symm
  · subst hx
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
    · have := hu.ntfn n hn; omega
    · have hv := nfootT_val (hT t ht) h
      have := hf2 t ht; have := (hT t ht).align; omega
  · have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have := congrArg UScalar.val hx
    rw [hkv] at this; omega
  · have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)]
    exact hI.st i hi
  · have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)]
    exact hI p hp
  · refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega)

/-- `XTopAt` at another arch state related to the same CR3. -/
theorem XTopAt.arch {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hAR : AR a' σ.archState.x64CurrentCr3) : XTopAt (L := L) AR Z s a' σ :=
  hX.frameStep (P1.WritesIn.refl s (fun _ => False)) (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) id
    rfl rfl rfl rfl rfl rfl rfl hX.fin.1.1.1 hX.fin.1.1.2.2.2.1 hX.fin.1.1.2.2.2.2.1 hX.rel.2.2.2.1 hAR

/-- **`copy_words` keeps an invariant** kept by each destination write. -/
theorem copy_words_inv (P : S → Prop) (s : S) (src dst n : U64) (hP : P s)
    (hstep : ∀ s (i : U64), P s → i.val < n.val → ∀ v,
      P (L.wr s (core.num.U64.wrapping_add dst (core.num.U64.wrapping_mul i 8#u64)) v)) :
    tcb.copy_words st s src dst n ⦃ s' => P s' ⦄ := by
  unfold tcb.copy_words tcb.copy_words_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => n.val - x.2.val)
    (inv := fun x => P x.1 ∧ x.2.val ≤ n.val)
  · rintro ⟨s1, i1⟩ ⟨h1, hi1⟩
    unfold tcb.copy_words_loop.body
    simp only [lift, bind_ok, L.read_eq, L.write_eq]
    split
    · rename_i hlt
      have hlt' : i1.val < n.val := by scalar_tac
      obtain ⟨j, hj, hjv⟩ := spec_exists (U64.add_spec (x := i1) (y := 1#u64) (by scalar_tac))
      rw [hj]; simp only [bind_ok, WP.spec_ok]
      refine ⟨⟨hstep s1 i1 h1 hlt' _, by scalar_tac⟩, by scalar_tac⟩
    · simp only [WP.spec_ok]; exact h1
  · exact ⟨hP, by simp⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The FPU work of ReadFPU and WriteFPU at `X`**: FL4's `fpu_transfer`
whose checks pass ends `Ok` at `X` after an outcome of the spec's
invocation from the restart's state. -/
def FpuHypX (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct p : U64)
    (c : tcb.Ctx) (toFrame blk call don : Bool) : Prop :=
  ∀ s1 σ1 (x ptr offset r asid va : U64) (m ep : Bool) (sz : capability.FrameSize),
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    Aeneas.Std.Array.index_usize c.extra 0#usize = ok x → x ≠ 0#u64 → ¬ c.length < 1#u64 →
    tcb.arg st s c 0#u64 = ok offset → capV (L.mem s) x = .Frame ptr sz r false m ep asid va →
    FpuPass toFrame offset r sz →
    tcb.fpu_transfer st arI s ar p c toFrame ⦃ res => res.1 = .Ok () ∧ ∃ σ',
      ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
          (.invokeFl4TCB (.fpuTransfer p.bv toFrame (ptr.bv + offset.bv)))).run σ1).1 ∧
      X res.2.1 res.2.2 σ' ⦄

set_option maxHeartbeats 4000000 in
/-- **`fpu_refines` at `X`** (TcbExt's, with `TopPostDMX`): the checks
proved, the decode errors at the start's `X`, the work `FpuHypX`. -/
theorem fpu_refinesX {AR : A → Fl4Spec.Cr3 → Prop} (X : S → A → Fl4Spec.State Unit → Prop)
    (hXX : ∀ s a σ, X s a σ → XTop (L := L) AR s a σ) (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (toFrame : Bool) (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hXa : X s ar σ) (blk don : Bool)
    (hF : FpuHypX (L := L) arI X s ar σ ct p ⟨length, buf, call, slot, extra⟩ toFrame blk call don) :
    tcb.fpu_transfer st arI s ar p ⟨length, buf, call, slot, extra⟩ toFrame ⦃ res =>
      TopPostDMX (L := L) X σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame (args.map UScalar.bv) p.bv excaps)) s res ⦄ := by
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have htr : excaps = [] ∨ args = [] →
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame (args.map UScalar.bv) p.bv excaps)).run σ =
        ({(.error .truncatedMessage, σ)}, False) := by
    intro h
    apply run_liftME_err
    unfold Fl4Spec.decodeFl4FpuTransfer
    rw [whenE_pos (by rcases h with h | h <;> simp [h])]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    unfold tcb.fpu_transfer
    rw [extra_eq _ 0#usize (by decide) hx0]
    simp only [h0, ↓reduceIte, error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage,
      htr (Or.inl (List.eq_nil_of_length_eq_zero (by omega))), Or.inl trivial⟩, hXa⟩)
  by_cases hl : length < 1#u64
  · unfold tcb.fpu_transfer
    rw [extra_eq _ 0#usize (by decide) hx0]
    simp only [h0, ↓reduceIte, error.truncated, bind_ok,
      show ¬ (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).length >= 1#u64 by show ¬ length >= 1#u64; scalar_tac]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage,
      htr (Or.inr (List.eq_nil_of_length_eq_zero (by scalar_tac))), Or.inl trivial⟩, hXa⟩)
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args, hlen with
    | y0 :: rest, _ => exact ⟨_, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨erest, rfl⟩ : ∃ erest, excaps = e0 :: erest := by
    match excaps, he0 with
    | a :: r, h => simp at h; exact ⟨r, by rw [h]⟩
  have hspec : (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame ((y0 :: rest).map UScalar.bv) p.bv
      (e0 :: erest)) =
      (match absCap (capV (L.mem s) x0) with
      | .archObjectCap (.pageCap dev base rights _ sz _) =>
        if dev ∨ rights = Fl4Spec.vmKernelOnly ∨ (toFrame ∧ rights ≠ Fl4Spec.vmReadWrite)
        then Fl4Spec.NonDetE.throwError (.invalidCapability 1)
        else do
          let size := 2 ^ Fl4Spec.pageBitsForSize sz
          Fl4Spec.NonDetE.whenE (y0.bv.toNat % 64 ≠ 0 ∨ y0.bv.toNat ≥ size ∨
              size - y0.bv.toNat < Fl4Spec.fl4FpuStateSize) <|
            Fl4Spec.NonDetE.throwError (.invalidArgument 0)
          Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.fpuTransfer p.bv toFrame (base + y0.bv))
      | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1)) := by
    unfold Fl4Spec.decodeFl4FpuTransfer
    rw [whenE_neg (by simp), retOk_bind, retOk_bind]
    simp only [List.map_cons, List.getElem?_cons_zero, the_some]
    rw [he01]; rfl
  have hcwf := (slot_wf hDS.1.1 hps0 hps01).1
  rw [← hxe0] at hcwf
  generalize hc : capV (L.mem s) x0 = c at hcwf hspec
  -- the checks passing: FL4's work
  have hfr : ∀ ptr sz r m ep asid va, c = .Frame ptr sz r false m ep asid va → FpuPass toFrame y0 r sz →
      tcb.fpu_transfer st arI s ar p ⟨length, buf, call, slot, extra⟩ toFrame ⦃ res =>
        TopPostDMX (L := L) X σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
          (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame ((y0 :: rest).map UScalar.bv) p.bv (e0 :: erest)))
          s res ⦄ := by
    intro ptr sz r m ep asid va hcf hpass
    subst hcf
    obtain ⟨s1, σ1, -, hs1, hst1, -, -, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    obtain ⟨hr1, hr3, hm, hlt, hrm⟩ := hpass
    obtain ⟨hw1, hw3⟩ := hcwf
    have hrg := frame_rights r hw1 hw3
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame ((y0 :: rest).map UScalar.bv) p.bv (e0 :: erest))).run σ =
        ({(.ok (.invokeFl4TCB (.fpuTransfer p.bv toFrame (ptr.bv + y0.bv))), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec]
      simp only [absCap]
      rw [if_neg (by
        rintro (h | h | ⟨h1, h2⟩)
        · cases h
        · exact hr1 (hrg.1.1 h)
        · exact h2 (hrg.2.2 (hr3 h1)))]
      rw [whenE_neg (by
        have hb : Fl4Spec.pageBitsForSize (frameSizeOf sz) = frameBitsN sz := by cases sz <;> rfl
        rw [hb, UScalar.bv_toNat]
        unfold FpuPass.fl4Spec_fpu at hrm
        omega), retOk_bind]
      rfl
    refine WP.spec_mono (hF s1 σ1 x0 ptr y0 r asid va m ep sz hs1 (by rw [← hcur]; exact hst1) hx0 h0 hl ha0 hc
      ⟨hr1, hr3, hm, hlt, hrm⟩) ?_
    rintro ⟨r2, s2, a2⟩ ⟨hr2, σ', hy, hXy⟩
    simp only at hr2 hXy; subst hr2
    obtain ⟨Z', hZ'⟩ := hXX _ _ _ hXy
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ'), hy, ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1,
      hZ'.rel.2.1, hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩, hXy⟩
  have hge : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).length >= 1#u64 := by show length >= 1#u64; scalar_tac
  have hic : ∀ (k : Unit → Fl4Spec.SEMonad Unit Fl4Spec.Fl4TcbInvocation),
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.Fl4TcbInvocation)).run σ =
        ({(.error (.invalidCapability 1), σ)}, False) := fun _ => run_liftME_err rfl
  have herr1 : ErrRel (.Sys (.InvalidCapability 1#u64)) (.invalidCapability 1) := Or.inr ⟨1#u64, rfl, rfl⟩
  cases c
  case Frame ptr sz r dev m ept asid va =>
    by_cases hpass : dev = false ∧ FpuPass toFrame y0 r sz
    · obtain ⟨rfl, hp⟩ := hpass; exact hfr _ _ _ _ _ _ _ rfl hp
    have hvk : capability.VM_KERNEL_ONLY = 1#u64 := by simp only [capability.VM_KERNEL_ONLY]
    have hvrw : capability.VM_READ_WRITE = 3#u64 := by simp only [capability.VM_READ_WRITE]
    obtain ⟨hw1, hw3⟩ := hcwf
    have hrg := frame_rights r hw1 hw3
    have hrun : ∀ tf : Bool, (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        ((Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidArgument 0) : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
          Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.fpuTransfer p.bv tf (ptr.bv + y0.bv)))).run σ =
        ({(.error (.invalidArgument 0), σ)}, False) := fun _ =>
      run_liftME_err (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidArgument 0) :
        Fl4Spec.SEMonad Unit Unit)) rfl _)
    have herr0 : ErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) := Or.inl rfl
    have hb : Fl4Spec.pageBitsForSize (frameSizeOf sz) = frameBitsN sz := by cases sz <;> rfl
    obtain ⟨z, hzv, hzf⟩ := fshift_eq sz
    unfold tcb.fpu_transfer
    rw [extra_eq _ 0#usize (by decide) hx0]
    simp only [h0, ↓reduceIte, hge, bind_ok]
    rw [ha0]; simp only [bind_ok]; rw [slot_cap_eq, capAt_capV, hc]; simp only [bind_ok, hvk, hvrw, hzf]
    by_cases hd : dev = true
    · simp only [hd, ↓reduceIte, error.invalid_cap, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, herr1⟩, hXa⟩)
      rw [hspec]; simp only [absCap]
      rw [if_pos (Or.inl hd)]; exact hic (fun _ => Fl4Spec.NonDetE.returnOk default)
    simp only [Bool.not_eq_true] at hd; subst hd
    by_cases hr1 : r = 1#u64
    · have hk : vmRightsOf r = Fl4Spec.vmKernelOnly := hrg.1.2 hr1
      simp only [hr1, ↓reduceIte, error.invalid_cap, bind_ok, Bool.false_eq_true]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, herr1⟩, hXa⟩)
      rw [hspec]; simp only [absCap]
      rw [if_pos (Or.inr (Or.inl hk))]; exact hic (fun _ => Fl4Spec.NonDetE.returnOk default)
    have hk : vmRightsOf r ≠ Fl4Spec.vmKernelOnly := fun h => hr1 (hrg.1.1 h)
    simp only [hr1, ↓reduceIte, Bool.false_eq_true]
    have hoff : (toFrame = true → r = 3#u64) →
        ¬ (y0.val % 64 = 0 ∧ y0.val < z.val ∧ 2696 ≤ z.val - y0.val) := by
      intro h3 h
      exact hpass ⟨rfl, hr1, h3, h.1, hzv ▸ h.2.1, by unfold FpuPass.fl4Spec_fpu Fl4Spec.fl4FpuStateSize; rw [← hzv]; exact h.2.2⟩
    have hoffS : (toFrame = true → r = 3#u64) →
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
          (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame ((y0 :: rest).map UScalar.bv) p.bv (e0 :: erest))).run σ =
          ({(.error (.invalidArgument 0), σ)}, False) := by
      intro h3
      rw [hspec]; simp only [absCap]
      rw [if_neg (by
        rintro (h | h | ⟨h1, h2⟩)
        · cases h
        · exact hk h
        · exact h2 (hrg.2.2 (h3 h1))), hb, whenE_pos (by
          have := hoff h3; rw [UScalar.bv_toNat, ← hzv]; unfold Fl4Spec.fl4FpuStateSize; omega)]
      exact hrun toFrame
    cases toFrame
    · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_arg, bind_ok]
      rw [off_fail _ _ y0 z (hoff (fun h => by cases h))]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, hoffS (fun h => by cases h), herr0⟩, hXa⟩)
    · by_cases hr3 : r = 3#u64
      · simp only [↓reduceIte, hr3, bne_self_eq_false, Bool.false_eq_true, error.invalid_arg, bind_ok]
        rw [off_fail _ _ y0 z (hoff (fun _ => hr3))]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, hoffS (fun _ => hr3), herr0⟩, hXa⟩)
      · simp only [↓reduceIte, bne_iff_ne, ne_eq, hr3, not_false_eq_true, error.invalid_cap, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, herr1⟩, hXa⟩)
        rw [hspec]; simp only [absCap]
        rw [if_pos (Or.inr (Or.inr ⟨trivial, fun h => hr3 (hrg.2.1 h)⟩))]
        exact hic (fun _ => Fl4Spec.NonDetE.returnOk default)
  all_goals
    unfold tcb.fpu_transfer
    rw [extra_eq _ 0#usize (by decide) hx0]
    simp only [h0, ↓reduceIte, hge, bind_ok]
    rw [ha0]; simp only [bind_ok]; rw [slot_cap_eq, capAt_capV, hc]
    simp only [bind_ok, error.invalid_cap]
    rw [hspec]
    simp only [absCap]
    try split_ifs
    all_goals exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, hic (fun _ => Fl4Spec.NonDetE.returnOk default),
      herr1⟩, hXa⟩)



theorem off_pass {α : Type} (E K : Result α) (y0 z : U64)
    (hpass : y0.val % 64 = 0 ∧ y0.val < z.val ∧ 2696 ≤ z.val - y0.val) :
    (do
      let i2 ← y0 % 64#u64
      if i2 != 0#u64 then E
      else if y0 >= z then E
      else do
        let i3 ← z - y0
        if i3 < fl4_abi.consts.FPU_STATE_SIZE then E else K) = K := by
  obtain ⟨hm0, h2', h3⟩ := hpass
  obtain ⟨m, hm, hmv⟩ := spec_exists (UScalar.rem_spec y0 (y := 64#u64) (by decide))
  rw [hm]; simp only [bind_ok]
  have hm00 : m = 0#u64 := by
    apply UScalar.eq_of_val_eq
    have e1 : m.val = y0.val % 64 := by rw [hmv]; rfl
    rw [e1, hm0]; rfl
  subst hm00
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have h2 : ¬ y0 >= z := by scalar_tac
  simp only [h2, ↓reduceIte]
  obtain ⟨d, hd, hdv⟩ := spec_exists (U64.sub_spec (x := z) (y := y0) (by scalar_tac))
  rw [hd]; simp only [bind_ok]
  have hfps : (fl4_abi.consts.FPU_STATE_SIZE).val = 2696 := by unfold fl4_abi.consts.FPU_STATE_SIZE; rfl
  have h4 : ¬ d < fl4_abi.consts.FPU_STATE_SIZE := by scalar_tac
  simp only [h4, ↓reduceIte]

/-- An X64 `storeWord` at the word `w` at byte offset `k` (`k + 8 ≤ 2696`)
from `F` leaves the bytes outside ReadFPU's 2696 bytes at `F`. -/
theorem fpu_store_other (um : Fl4Spec.Word → Fl4Spec.Word8) (F : Fl4Spec.Word) (w : U64) (k : Nat)
    (hk : k + 8 ≤ 2696) (hw : w.val = (F.toNat + k) % 2 ^ 64) (v a : Fl4Spec.Word)
    (ha : 2696 ≤ (a - F).toNat) : Endp.storeMem um w.bv v a = um a := by
  refine Endp.storeMem_other um _ v a fun y hy e => ?_
  subst e
  have h1 : w.bv.toNat = w.val := rfl
  have h2 := F.isLt
  have h3 := w.bv.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_add, h1, hw] at ha
  simp only [Nat.reducePow] at ha h2 h3
  omega

/-- **The user frame's words written by ReadFPU at `XTop`** [W] (with [J]:
the frame's words lie outside the kernel's objects): FL4's copy of the
TCB's FPU image into the frame keeps `XTopAt` at the spec state whose user
memory is some `um` agreeing with the old one outside the 2696 bytes at the
frame (`Fl4Spec.fl4FpuToFrame`'s outcomes). -/
def FpuFrameXHyp (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (p frame : U64) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), XTopAt (L := L) AR Z s a σ →
    tcb.copy_words st s (core.num.U64.wrapping_add p layout.tcb.FPU) frame 337#u64 ⦃ s' =>
      ∃ um : Fl4Spec.Word → Fl4Spec.Word8,
        (∀ a : Fl4Spec.Word, 2696 ≤ (a - frame.bv).toNat → um a = σ.machineState.underlyingMemory a) ∧
        XTopAt (L := L) AR Z s' a (Endp.setUm σ um) ⦄

/-- **`FpuFrameXHyp` from the frame's words being IPC-buffer words** [J]
(the words of a spec data page, each `(w, w)` in `B`: JointAt's
`FrameCover`; `BufPlaced` [J]): each word written by `bufw_inv`, the spec's
memory stored as FL4's at the same address. -/
theorem fpuFrameX_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (p frame : U64)
    (hUW : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), XTopAt (L := L) AR Z s a σ →
      (∀ i : U64, i.val < 337 →
        (core.num.U64.wrapping_add frame (core.num.U64.wrapping_mul i 8#u64),
          (core.num.U64.wrapping_add frame (core.num.U64.wrapping_mul i 8#u64)).bv) ∈ Z.B) ∧
      BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ) :
    FpuFrameXHyp (L := L) AR Z p frame := by
  intro s a σ hX
  refine copy_words_inv (fun s' => ∃ um : Fl4Spec.Word → Fl4Spec.Word8,
      (∀ a : Fl4Spec.Word, 2696 ≤ (a - frame.bv).toNat → um a = σ.machineState.underlyingMemory a) ∧
      XTopAt (L := L) AR Z s' a (Endp.setUm σ um)) s _ frame _
    ⟨σ.machineState.underlyingMemory, fun _ _ => rfl, hX⟩ ?_
  rintro s2 i ⟨um, hag, h2⟩ hi v
  obtain ⟨hu, hBP⟩ := hUW _ _ _ h2
  have hwB := hu i hi
  have hI := bufw_inv (L := L) s2 a _ h2.toRInv hBP hwB v
  have hiv : (core.num.U64.wrapping_add frame (core.num.U64.wrapping_mul i 8#u64)).val =
      (frame.bv.toNat + 8 * i.val) % 2 ^ 64 := by
    have : i.val < 337 := hi
    have e : frame.bv.toNat = frame.val := rfl
    have e8 : (8#u64 : U64).val = 8 := rfl
    have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [UScalar.size_def, UScalarTy.numBits]
    rw [e]
    simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, e8, hs]
    omega
  refine ⟨Endp.storeMem um (core.num.U64.wrapping_add frame (core.num.U64.wrapping_mul i 8#u64)).bv v.bv,
    fun b hb => ?_, h2.ofRInv hI (L.ksb_wr _ _ _) (Sched.SzKeep.of_kheap rfl)⟩
  rw [fpu_store_other um frame.bv _ (8 * i.val) (by have : i.val < 337 := hi; omega) hiv v.bv b hb]
  exact hag b hb

set_option maxHeartbeats 8000000 in
/-- **The FPU work at `XTop`** (`FpuHypX`): the restart, `fpu_flush`, the
copy (WriteFPU: into the TCB's FPU image, `XTopAt.tcbWrF`; ReadFPU: into the
frame, `FpuFrameXHyp` [W]), `fpu_sanitise` and `fpu_reload` (WriteFPU); the
arch relation kept by the FPU operations (`ARKeep`, part of `ARIface` [P]). -/
theorem fpuHypX_of {AR : A → Fl4Spec.Cr3 → Prop} (hARI : ARKeep arI AR) {Z : XSets} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (ct p : U64)
    (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (hpT : p ∈ Z.T)
    (c : tcb.Ctx) (toFrame blk call don : Bool)
    (hFr : toFrame = true → ∀ (x ptr offset r : U64) (sz : capability.FrameSize) (m ep : Bool) (asid va : U64),
      capV (L.mem s) x = .Frame ptr sz r false m ep asid va → FpuPass toFrame offset r sz →
      FpuFrameXHyp (L := L) AR Z p (core.num.U64.wrapping_add ptr offset)) :
    FpuHypX (L := L) arI (XTop (L := L) AR) s ar σ ct p c toFrame blk call don := by
  intro s1 σ1 x ptr offset r asid va m ep sz hs1 hst1 hx hx0 hl ho hc hpass
  obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hs1 hst1
  have hAR1 := hX1.fin.1.1.2.2.2.2.2.2
  obtain ⟨hr1, hr3, hm, hlt, hrm⟩ := hpass
  have hvk : capability.VM_KERNEL_ONLY = 1#u64 := by simp only [capability.VM_KERNEL_ONLY]
  have hvrw : capability.VM_READ_WRITE = 3#u64 := by simp only [capability.VM_READ_WRITE]
  obtain ⟨z, hzv, hzf⟩ := fshift_eq sz
  have hge : c.length >= 1#u64 := by scalar_tac
  have hrc : tcb.restart_caller st s = ok s1 := by
    unfold tcb.restart_caller; rw [hct]; simp only [bind_ok]; exact hs1
  have hsz : fl4_abi.consts.FPU_STATE_SIZE + 7#u64 = ok 2703#u64 := by
    unfold fl4_abi.consts.FPU_STATE_SIZE
    obtain ⟨v, hv, hvv⟩ := spec_exists (U64.add_spec (x := 2696#u64) (y := 7#u64) (by scalar_tac))
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv]; rfl
  have hwd : (2703#u64 : U64) / 8#u64 = ok 337#u64 := by
    obtain ⟨v, hv, hvv⟩ := spec_exists (U64.div_spec (x := 2703#u64) (y := 8#u64) (by decide))
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv]; rfl
  obtain ⟨Q, R0, hcq, -⟩ := hX1.fin.1.1.1.lists
  have hpf := (hcq.tcbs p hpT).fits
  have hpa := (hcq.tcbs p hpT).align
  have hfpu : (core.num.U64.wrapping_add p layout.tcb.FPU).val = p.val + 512 := by
    unfold layout.tcb.FPU
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  -- the copy into the TCB's FPU image keeps `XTopAt`
  have hcopyT : ∀ (s0 : S) (a0 : A) (src : U64), XTopAt (L := L) AR Z s0 a0 σ1 →
      tcb.copy_words st s0 src (core.num.U64.wrapping_add p layout.tcb.FPU) 337#u64 ⦃ s' =>
        XTopAt (L := L) AR Z s' a0 σ1 ⦄ := by
    intro s0 a0 src h0
    refine copy_words_inv (fun s' => XTopAt (L := L) AR Z s' a0 σ1) s0 src _ _ h0 ?_
    intro s2 i h2 hi v
    have hiv : (core.num.U64.wrapping_mul i 8#u64).val = 8 * i.val := by
      simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
      have : i.val < 337 := hi
      omega
    refine h2.tcbWrF hpT _ (512 + 8 * i.val) ⟨by omega, by have : i.val < 337 := hi; omega, by omega⟩ ?_ v
    have : i.val < 337 := hi
    have h1 : (core.num.U64.wrapping_add p layout.tcb.FPU).val + (core.num.U64.wrapping_mul i 8#u64).val < 2 ^ 64 := by
      rw [hfpu, hiv]; omega
    clear h1
    unfold layout.tcb.FPU
    simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
    simp [U64.size, U64.numBits]
    omega
  unfold tcb.fpu_transfer
  rw [extra_eq _ 0#usize (by decide) hx]
  simp only [hx0, ↓reduceIte, hge, bind_ok]
  rw [ho]; simp only [bind_ok]; rw [slot_cap_eq, capAt_capV, hc]; simp only [bind_ok, hvk, hvrw, hzf]
  simp only [Bool.false_eq_true, ↓reduceIte, hr1]
  have hp' : offset.val % 64 = 0 ∧ offset.val < z.val ∧ 2696 ≤ z.val - offset.val := by
    unfold FpuPass.fl4Spec_fpu Fl4Spec.fl4FpuStateSize at hrm
    exact ⟨hm, hzv ▸ hlt, hzv ▸ hrm⟩
  cases toFrame
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [off_pass _ _ offset z hp']
    rw [hrc]; simp only [bind_ok]
    refine WP.spec_bind (hARI.fpu_flush ar p _ hAR1) fun a1 ha1 => ?_
    simp only [hsz, hwd, bind_ok, lift, obj.Tcb.fpu_addr]
    refine WP.spec_bind (hcopyT s1 ar _ hX1) fun s2 h2 => ?_
    try simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (hARI.fpu_sanitise a1 p _ ha1) fun a2 ha2 => ?_
    refine WP.spec_bind (hARI.fpu_reload a2 p _ ha2) fun a3 ha3 => ?_
    refine (WP.spec_ok _).2 ⟨rfl, σ1, rfl, ⟨Z, h2.arch ha3⟩⟩
  · simp only [↓reduceIte, hr3, bne_self_eq_false, Bool.false_eq_true]
    rw [off_pass _ _ offset z hp']
    rw [hrc]; simp only [bind_ok]
    refine WP.spec_bind (hARI.fpu_flush ar p _ hAR1) fun a1 ha1 => ?_
    simp only [hsz, hwd, bind_ok, lift, obj.Tcb.fpu_addr]
    refine WP.spec_bind (hFr rfl x ptr offset r sz m ep asid va hc ⟨hr1, hr3, hm, hlt, hrm⟩ s1 a1 σ1 (hX1.arch ha1)) ?_
    rintro s2 ⟨um, hag, h2⟩
    try simp only [↓reduceIte]
    refine (WP.spec_ok _).2 ⟨rfl, Endp.setUm σ1 um, ?_, ⟨Z, h2⟩⟩
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    refine mem_liftE (x := ([], Endp.setUm σ1 um)) ?_
    refine mem_bind_nd (x := ((), Endp.setUm σ1 um)) ?_ (Set.mem_singleton_iff.2 rfl)
    have hfb : (core.num.U64.wrapping_add ptr offset).bv = ptr.bv + offset.bv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      show (core.num.U64.wrapping_add ptr offset).val = (ptr.val + offset.val) % 2 ^ 64
      simp only [core.num.U64.wrapping_add_val_eq]
      simp [U64.size, U64.numBits]
    exact dmo_ex _ σ1 (fpuToFrame_mem _ σ1.machineState um fun b hb => hag b (by rw [hfb]; exact hb))

set_option maxHeartbeats 4000000 in
/-- **TcbXOpen3's ReadFPU and WriteFPU at `XTop`** (`toFrame` for ReadFPU):
`fpu_refinesX` with `fpuHypX_of`. -/
theorem tcb_fpuX {AR : A → Fl4Spec.Cr3 → Prop} (hAK : ARKeep arI AR) {Z : XSets} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hDI : DelInv Z.th (L.mem s))
    (p : U64) (hpT : p ∈ Z.T) (toFrame : Bool) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some (if toFrame then .readFpu else .writeFpu))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hFr : toFrame = true → ∀ (x ptr offset r : U64) (sz : capability.FrameSize) (m ep : Bool) (asid va : U64),
      capV (L.mem s) x = .Frame ptr sz r false m ep asid va → FpuPass toFrame offset r sz →
      FpuFrameXHyp (L := L) AR Z p (core.num.U64.wrapping_add ptr offset))
    (blk don : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ (if toFrame then fl4_abi.label.TCBReadFPU else fl4_abi.label.TCBWriteFPU)
      p ⟨length, buf, call, slot, extra⟩ blk call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame (args.map UScalar.bv) p.bv excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]
    cases toFrame <;> rfl
  unfold TcbOKX
  have he := decode_fpu_eq arI s ar p ⟨length, buf, call, slot, extra⟩ hstall
  rw [hdec0]
  have hF := fpuHypX_of arI hAK s ar σ hX hC ct p hct hcur hpT ⟨length, buf, call, slot, extra⟩ toFrame blk call don hFr
  cases toFrame
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [he.2]
    exact fpu_refinesX arI (XTop (L := L) AR) (fun _ _ _ h => h) Z.th hP s ar σ Z.G hDS hX.rel.2.2.2.2.1 p false
      length buf ct hct args hlen hargs hcur htcb hact call slot extra x0 x1 x2 hx0 excaps hXc ⟨Z, hX⟩ blk don hF
  · simp only [↓reduceIte]; rw [he.1]
    exact fpu_refinesX arI (XTop (L := L) AR) (fun _ _ _ h => h) Z.th hP s ar σ Z.G hDS hX.rel.2.2.2.2.1 p true
      length buf ct hct args hlen hargs hcur htcb hact call slot extra x0 x1 x2 hx0 excaps hXc ⟨Z, hX⟩ blk don hF

/-- **The Thread cap's label still open** [W] once ReadFPU and WriteFPU are
proved: SetTimer. -/
structure TcbXOpen1 (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) : Prop where
  setTimer : lbl = fl4_abi.label.TCBSetTimer →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer

/-- **`TcbXOpen3` with ReadFPU and WriteFPU proved** (`tcb_fpuX`): the extra
caps (`XcRel` [W]), the arch relation across the FPU operations (`ARKeep`
[P]), ReadFPU's user-frame write (`FpuFrameXHyp` [W]). -/
theorem tcbXOpen3_of {AR : A → Fl4Spec.Cr3 → Prop} (hAK : ARKeep arI AR) {Z : XSets} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s)) (lbl length : U64) (p : U64)
    (hp : Z.th p = some .tcb) (blk call don : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hFr : ∀ (x ptr offset r : U64) (sz : capability.FrameSize) (m ep : Bool) (asid va : U64),
      capV (L.mem s) x = .Frame ptr sz r false m ep asid va → FpuPass true offset r sz →
      FpuFrameXHyp (L := L) AR Z p (core.num.U64.wrapping_add ptr offset))
    (hO : TcbXOpen1 (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer) :
    TcbXOpen3 (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer := by
  refine ⟨?_, ?_, hO.setTimer⟩
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .readFpu by
      simp [tcbExtOf])
    exact tcb_fpuX arI hAK s ar σ hX hC hDI p (hTh p hp) true slbl hg he length buf ct hct argsU hlen hargs hcur hact
      (hstall' p) call _ extra x0 x1 x2 hx0 excaps hXc (fun _ => hFr) blk don ci sl buffer
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .writeFpu by
      simp [tcbExtOf])
    exact tcb_fpuX arI hAK s ar σ hX hC hDI p (hTh p hp) false slbl hg he length buf ct hct argsU hlen hargs hcur hact
      (hstall' p) call _ extra x0 x1 x2 hx0 excaps hXc (fun h => absurd h (by decide)) blk don ci sl buffer

end

end

end Fl4Proofs.P3
