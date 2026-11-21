/-
P3 (DESIGN.md §9), CSpace: **the debug-list words the deletion loop's
steps keep at `J`** (`DbgKeep`, P1's QueueDbgKeep: the kernel-state base
and every TCB's `DEBUG_NEXT` / `DEBUG_PREV` word and every core's
`DEBUG_TCBS` head word kept), toward carrying DbgWF's `DbgWF` through the
loop (only a thread cap's finalisation, by `debug_remove`, changes them).

* `dbgKeep_of_writes`: writes avoiding the debug words keep them;
  `JAtZ.notDbg`: a word outside every TCB of `H` and every core's node is no
  debug word.
* `JAtZ.finVsDbg`: a VSpace finalisation (VsFin's `vs_fin`: native VSpace
  caps, VSpace-mapped frames, a mapped EPT root's `delete_asid`) writes
  `VsW` words only (`JAtZ.vsObjW`, `JAtZ.vsNodeW`).
* `JAtZ.frVtDbg`, `JAtZ.finEptDbg`, `JAtZ.finVcpuDbg`: the VT-x work
  (XTopJointFinVtJ's steps: EPT-mapped frames, owned IO ports, EPT and VCPU
  caps) writes `VtOut` words and the VCPU list's head only (`VtOut.obj`,
  `.node`, `JAtZ.vHead_notDbg`).
* `fin_idle_dbg`: a finalisation with no work (non-final caps, unmapped
  frames, unowned IO ports; DelObj's `fin_idle`) keeps the state.
* `JAtZ.slotFrame_dbgKeep`: the loop's slot edits (`SlotFrame2`: swap,
  zombie write, empty, also the IRQ handler's nested `delete_one`'s empty)
  write slot words only, none a debug word (`JAtZ.inSlot_notDbg`: a TCB's
  slots below its offset 256, `SlotsApart`; every slot apart from every
  core's node, `JAtZ.slot_node` from `JKern.hnd`).
* `JAtZ.ppDbg`: the preemption point (P1's `preemption_point.pp`:
  `WORK_UNITS`, the current node's `CUR_TIME`/`CONSUMED`); `JAtZ.postDbg`:
  `post_cap_deletion` (`KsW` words, `JAtZ.ksW_notDbg`).
* A final thread cap: `fin_thread.dbgPre` (the steps of P1's
  `fin_thread.blk` before `debug_remove` keep the debug words, their `KW`
  footprints; then `debug_remove_mem` at that state; no word written
  after), `JAtZ.finThreadDbgPre` at `J.blk`; `dbgWF_thread` /
  `JAtZ.dbgWF_thread`: `DbgWFL` after with the thread erased from its
  core's list (`dbgRm_wf`; the affinities at the intermediate state from
  `JAtZ` after, every TCB on the current core, `SchedCore.aff`).
* Not needing a lemma here: the endpoint, notification, SC and reply
  finalisers (P1's QueueDbgKeep, at `J.blk`; the reply's `hdc` from
  `SchedRel.aff`/`.core`), the IRQ handler's (a notification finalisation
  then an empty).
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.XTopJointPP
import Fl4Proofs.P3.XTopJointPost
import Fl4Proofs.P3.DbgWF
import Fl4Proofs.P1.QueueDbgKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

/-- A `VtOut` word is no debug word. -/
theorem JAtZ.vtOut_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : VtOut (L := L) Z H Cs s σ b) : ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b :=
  J.notDbg (fun p hp => hb.obj p .tcb hp (fun z h => by cases h)) hb.node

/-- The VCPU list's head word is no debug word (it lies below the nodes). -/
theorem JAtZ.vHead_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s (P1.vHeadA st s) := by
  have hf := J.kern.ksbFit
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val hf
  refine J.notDbg (fun p hp => ?_) (fun c _ => ?_)
  · obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
    have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
    rw [hv, e12]
    rcases hq.ksOut p hp with h | h <;> omega
  · have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
    left; rw [hv, hnb]; omega

set_option maxHeartbeats 16000000 in
/-- **A VSpace finalisation keeps the debug words** (`vs_fin`'s `VsW`
footprint, as `JAtZ.finVsJb`). -/
theorem JAtZ.finVsDbg [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Ap : VsApart (L := L) Z H Cs s)
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hDS : DState (L := L) Z.th s σ Z.G) (hAs : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hvf : IsVsFin c) (b : Bool) (hw : FinWork c b) :
    objects.finalise_cap st arI s a c b false ⦃ r => P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.2.1 ⦄ := by
  have hS := J.xtop.fin.1
  have hH : VsFinHyps st A arI Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1
      (FootSR st (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s (VsW Z (L.ksb s))) :=
    VsFinHyps.footN (fun _ h => Or.inl h) (fun _ h => Or.inr h) (vsFinHyps_top hA)
  refine WP.spec_mono (vs_fin hH s a σ Z.G sl hDS hAs
    ⟨hS.2.pl, hS.2.pt, hS.2.ps, hS.2.pv, hS.2.po, hS.2.vo, hS.2.sd, hS.2.vs,
      ⟨⟨hS, P1.WritesIn.refl _ _⟩, J.xtop.fin.2⟩, J.vsc⟩ c hc hvf b hw) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨-, -, -, -, -, -, -, -, -, -, ⟨-, hW⟩, -⟩, -⟩
  simp only at hW ⊢
  exact dbgKeep_of_writes J.blk hW fun b hb =>
    J.notDbg (fun p hp => J.vsObjW Ap hb hp (fun z h => by cases h)) (fun c hc => J.vsNodeW hb hc)

set_option maxHeartbeats 4000000 in
/-- **The VT-x work of a finalisation keeps the debug words** (as
`JAtZ.frVtJ`: `ept::unmap`, `revoke_ports`, `VtOut` words only). -/
theorem JAtZ.frVtDbg [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) (hK : ARKeep arI AR) {s : S} {a : A}
    {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {c : capability.Cap} {x : U64} (hx : IsSlot Z.th x) (hcv : capV (L.mem s) x = c) (hk : FrVtK c) (b : Bool) :
    objects.finalise_cap st arI s a c b false ⦃ r => P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.2.1 ⦄ := by
  have har := J.xtop.fin.1.1.2.2.2.2.2.2
  rcases hk with ⟨p, sz, r, d, asid, va, rfl⟩ | ⟨f, l, o, rfl, ho⟩
  · obtain ⟨i, hi⟩ : ∃ i, capability.FrameSize.bits sz = ok i := by cases sz <;> exact ⟨_, rfl⟩
    simp only [objects.finalise_cap, objects.finalise_cap_object, P1.plain_retire, bind_ok, ↓reduceIte, hi,
      ite_self]
    split
    · refine WP.spec_bind (ept_unmap_vt hA a har asid va p i false (X := VtOut (L := L) Z H Cs s σ)
        (fun x hx => hx.al) (hV.ept Z H Cs Ac Lst D s a σ rfl J _ hx (by rw [hcv]; simp [Vs.NativeCap]) asid)) ?_
      rintro ⟨s1, a1⟩ ⟨hw, -⟩
      try simp only [uncurry_apply_pair]
      exact (WP.spec_ok _).2 (dbgKeep_of_writes J.blk hw fun b hb => J.vtOut_notDbg hb)
    · try simp only [P1.plain_retire, ite_self, bind_ok, uncurry_apply_pair]
      exact (WP.spec_ok _).2 (P1.DbgKeep.refl s)
  · have P := hV.io Z H Cs Ac Lst D s a σ rfl J _ hx (by rw [hcv]; exact ho)
    simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    refine WP.spec_bind (revoke_ports_vt hK J P o f l) ?_
    rintro ⟨s1, a1⟩ ⟨hw, -⟩
    have hD := dbgKeep_of_writes J.blk hw fun b hb => J.vtOut_notDbg (VIoW.vt P hb)
    try simp only [uncurry_apply_pair]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 hD
    · simp only [↓reduceIte]
      exact (WP.spec_ok _).2 hD

set_option maxHeartbeats 4000000 in
/-- **A final EPT cap's finalisation keeps the debug words** (as
`JAtZ.finEptJ`). -/
theorem JAtZ.finEptDbg (hA : ArchRefines arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {c : capability.Cap} {x : U64} (hx : IsSlot Z.th x) (hcv : capV (L.mem s) x = c) (hk : EptK c) :
    objects.finalise_cap st arI s a c true false ⦃ r => P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.2.1 ⦄ := by
  obtain ⟨p, lv, m, asid, va, rfl, hnr⟩ := hk
  have har := J.xtop.fin.1.1.2.2.2.2.2.2
  cases m
  · have he : objects.finalise_cap st arI s a (.Ept p lv false asid va) true false = ok ((.Null, .Null), s, a) := by
      simp [objects.finalise_cap, objects.finalise_cap_object, ept.finalise]
    rw [he, WP.spec_ok]
    exact P1.DbgKeep.refl s
  · have hl0 : lv ≠ 0#u64 := fun e => hnr ⟨rfl, e⟩
    simp only [objects.finalise_cap, objects.finalise_cap_object, ept.finalise, bind_ok, ↓reduceIte, hl0]
    refine WP.spec_bind (ept_unmap_vt hA a har asid va p lv true (X := VtOut (L := L) Z H Cs s σ)
      (fun x hx => hx.al) (hV.ept Z H Cs Ac Lst D s a σ rfl J _ hx (by rw [hcv]; simp [Vs.NativeCap]) asid)) ?_
    rintro ⟨s1, a1⟩ ⟨hw, -⟩
    try simp only [uncurry_apply_pair]
    exact (WP.spec_ok _).2 (dbgKeep_of_writes J.blk hw fun b hb => J.vtOut_notDbg hb)

set_option maxHeartbeats 4000000 in
/-- **A final VCPU cap's finalisation keeps the debug words** (as
`JAtZ.finVcpuJ`: `VtOut` words and the VCPU list's head). -/
theorem JAtZ.finVcpuDbg (hK : ARKeep arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap}
    (hA' : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : VcpuK c) :
    objects.finalise_cap st arI s a c true false ⦃ r => P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.2.1 ⦄ := by
  obtain ⟨v, rfl⟩ := hk
  have hcv := capV_of_capAt hc
  have har := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨h0, hp, hn, -⟩ := hV.vcpu Z H Cs Ac Lst D s a σ rfl J _ v hA'.isSlot hcv
  have hha : P1.Aligned (P1.vHeadA st s) := by
    have hf := J.kern.ksbFit
    have hal := J.kern.ksbAl
    have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val hf
    unfold P1.Aligned; rw [hv]; omega
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (vcpu_finalise_vt hK v a har h0 hha (X := VtOut (L := L) Z H Cs s σ)
    (fun h => ⟨hp h, (hp h).al⟩) (fun h => ⟨hn h, (hn h).al⟩)) ?_
  rintro ⟨s1, a1⟩ ⟨hw, -⟩
  try simp only [uncurry_apply_pair]
  refine (WP.spec_ok _).2 (dbgKeep_of_writes J.blk hw fun b hb => ?_)
  rcases hb with hb | rfl
  · exact J.vtOut_notDbg hb
  · exact J.vHead_notDbg

/-- **The deletion loop's slot edits keep the debug words** (a
`SlotFrame2` step: swap, zombie write, empty). -/
theorem JAtZ.slotFrame_dbgKeep {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hF : Vs.SlotFrame2 (L := L) Z.th s s') :
    P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
  dbgKeep_of_writes J.blk (SlotFrame2.writesIn hF) fun _ hb => J.inSlot_notDbg (slotWd_range J.xtop.rel.1 hb)

/-- **The preemption point keeps the debug words** (P1's
`preemption_point.pp`: `WORK_UNITS` and the current node's `CUR_TIME`,
`CONSUMED`). -/
theorem JAtZ.ppDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hA : P0.ArchTotal arI) :
    sched.preemption_point st arI s a ⦃ r => P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.2.1 ⦄ :=
  WP.spec_mono (P1.sched.preemption_point.pp hA s a J.blk) fun r ⟨_, hw⟩ => dbgKeep_of_writes J.blk hw fun b hb => by
    have hf := J.kern.ksbFit
    have hcpu := J.kern.cpuCs
    rcases hb with rfl | rfl | rfl
    · have hv := workUnits_val hf
      exact J.ksW_notDbg ⟨40#u64, by decide, by decide, by decide, by rw [hv]; rfl, Or.inl (by decide)⟩
    · exact P1.dbgW_not_kw J.blk (Or.inr (Or.inl ⟨L.cpu s, hcpu, layout.node.CUR_TIME,
        by simp [layout.node.CUR_TIME], by simp [layout.node.CUR_TIME], rfl⟩))
    · exact P1.dbgW_not_kw J.blk (Or.inr (Or.inl ⟨L.cpu s, hcpu, layout.node.CONSUMED,
        by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], rfl⟩))

set_option maxHeartbeats 4000000 in
/-- **A cleanup cap's `post_cap_deletion` keeps the debug words**
(XTopPostDel's `post_irqX`, `post_ioX`: `KsW` words only). -/
theorem JAtZ.postDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hAM : ARMask arI AR) (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a') {cl : capability.Cap}
    (hcl : CleanCap cl) (hcln : cl ≠ .Null) (hclw : CapWf cl) :
    objects.post_cap_deletion st arI s a cl ⦃ r => P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.1 ⦄ := by
  have hX := J.xtop
  cases cl <;> simp only [CleanCap] at hcl
  · exact absurd rfl hcln
  · refine WP.spec_mono (post_irqX arI hAM hX J.ks J.intL hmask hfree _ hclw) ?_
    rintro r ⟨-, -, σ', -, -, hw, -, -⟩
    exact dbgKeep_of_writes J.blk hw fun _ hb => J.ksW_notDbg hb
  · obtain ⟨hf, hl, hfl⟩ := hclw
    refine WP.spec_mono (post_ioX arI hX J.ks J.ioLay _ _ _ hfl hl) ?_
    rintro r ⟨-, -, σ', -, -, hw, -, -⟩
    exact dbgKeep_of_writes J.blk hw fun _ hb => J.ksW_notDbg hb

end

/-! ## A thread cap's finalisation -/

section Thr
open Fl4Proofs.P0.Consts
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {T : Set U64} {Ω : Set U64} {H : P1.Heap}
  {Cs Sg Rp Scs Nt : Set U64} {Zb : U64 → Nat} {Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A final thread cap's finalisation, for the debug words** (the steps
of P1's `fin_thread.blk`): the steps before `debug_remove` keep the debug
words (their `KW` footprints, `Foot.dbgKeep`), then `debug_remove` from
that state `s5` (`debug_remove_mem`), then no word written. -/
theorem fin_thread.dbgPre {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (fin : Bool) (h : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Zb Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r => fin = true → ∃ s5 : S,
      P1.DbgKeep st T Cs s s5 ∧ (∀ c ∈ Cs, P1.NodePlaced st T s5 c) ∧ L.mem s5 (P1.affA p) ∈ Cs ∧
      P1.DbgTz st T Cs s5 ∧ L.ksb r.2.1 = L.ksb s5 ∧
      ∀ b, P1.Aligned b → L.mem r.2.1 b = dbgRmM (L.mem s5) (dbgHd (L := L) s5 (L.mem s5 (P1.affA p))) p b ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · rename_i hf0
    exact (WP.spec_ok _).2 fun hf => absurd hf hf0
  have hStart := h
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hStart
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a p h)
    (smp.remote_tcb_stall.all hA s a p hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, -, ei1⟩, _, _, _, _, _, _, _, _, _, keep, _⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (vcpu.detach_none ar s1 a1 p (by
    rw [keep p hp 3664#u64 (by simp) (by simp)]; exact hv0)) ?_
  intro r hr
  subst r
  try dsimp only
  refine WP.spec_bind (notification.unbind_notification.blkF s1 p h1 hp) fun s2 ⟨h2, f2, n2⟩ => ?_
  refine WP.spec_bind (timer.remove.tf (s0 := s2) s2 p (TF.start h2) hp) fun s3 ⟨h3, f3, n3, k3, _⟩ => ?_
  have ea3 : L.actionW s3 = L.actionW s := by rw [n3.1, n2.1, ea1]
  have ei3 : L.idleW s3 = L.idleW s := by rw [n3.2.1, n2.2.1, ei1]
  have f03 : Foot st T Cs Sg Scs Zb ∅ s s3 := f1.trans (f2.trans f3)
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Zb Ac r.1 ∧
      Foot st T Cs Sg Scs Zb ∅ s r.1 ∧ L.actionW r.1 ≠ p) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, f03, by rw [ea3]; exact hna⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (schedcontext.unbind_tcb.blk s3 i h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
      (fun _ => by rw [hit, ei3]; exact hidle)) fun s5 hh5 => ?_
    obtain ⟨h5, f5, ea5, _⟩ := hh5
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, f03.trans f5, na5⟩
    · have hiS5 : i ∈ Scs := hiS
      refine WP.spec_mono (schedcontext.complete_yield_to.blk hA s5 a1 y h5 (fun hy0 => by
        rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS5 (by rw [← ey]; exact hy0))) ?_
      rintro ⟨s6, a6⟩ ⟨h6, f6, n6⟩
      exact ⟨h6, (f03.trans f5).trans f6, by rw [n6.1]; exact na5⟩
  rintro ⟨s4, a2⟩ ⟨h4, f4, na4⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.suspend.blk s4 a2 p h4 hp na4) ?_
  rintro ⟨s5, a3⟩ ⟨h5, f5⟩
  try simp only [WP.uncurry'_pair]
  have hq5 := h5.1.choose_spec.choose_spec
  have hTz5 : P1.DbgTz st T Cs s5 := ⟨h5.2.2.1.2.2.tm.dn, h5.2.2.1.2.2.tm.dp, h5.2.2.1.2.2.tm.dh⟩
  refine WP.spec_bind (debug_remove_mem s5 p hq5.tcbs hq5.nodes hTz5 (hq5.aff p hp) hp) fun s6 ⟨hk6, hm6⟩ => ?_
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  exact (WP.spec_ok _).2 fun _ => ⟨s5, P1.Foot.dbgKeep h (fun _ h => h) ((f4.mono (Set.empty_subset _)).trans f5),
    hq5.nodes, hq5.aff p hp, hTz5, hk6, hm6⟩

/-- **The debug lists after a thread's finalisation** (`fin_thread.dbgPre`'s
facts, the affinities kept): the thread erased from its core's list. -/
theorem dbgWF_thread {s s5 r : S} {p : U64} {lst : U64 → List U64}
    (hT : P1.TcbPlaced T) (hW : DbgWFL T Cs (L.mem s) (dbgHd (L := L) s) lst) (hK : P1.DbgKeep st T Cs s s5)
    (hN5 : ∀ c ∈ Cs, P1.NodePlaced st T s5 c) (hp : p ∈ T) (hc5 : L.mem s5 (P1.affA p) ∈ Cs)
    (hD5 : P1.DbgTz st T Cs s5) (hkr : L.ksb r = L.ksb s5)
    (hm : ∀ b, P1.Aligned b → L.mem r b = dbgRmM (L.mem s5) (dbgHd (L := L) s5 (L.mem s5 (P1.affA p))) p b)
    (haff : ∀ y ∈ T, L.mem r (P1.affA y) = L.mem s (P1.affA y)) :
    DbgWFL T Cs (L.mem r) (dbgHd (L := L) r) (fun c => (lst c).erase p) := by
  have hd5 : dbgHd (L := L) s5 = dbgHd (L := L) s := dbgHd_of_ksb hK.1
  have hA5 := dbgApart_of (L := L) hT hN5
  have hal : ∀ y ∈ T, P1.Aligned (P1.dnA y) ∧ P1.Aligned (P1.dpA y) ∧ P1.Aligned (P1.affA y) := fun y hy =>
    ⟨P1.field_aligned (hT y hy) (by simp) (by simp), P1.field_aligned (hT y hy) (by simp) (by simp),
      P1.field_aligned (hT y hy) (by simp) (by simp)⟩
  have hpT : L.mem s5 (P1.dpA p) ≠ 0#u64 → L.mem s5 (P1.dpA p) ∈ T := fun h => (hD5.dp p hp).ne0 h
  have hnT : L.mem s5 (P1.dnA p) ≠ 0#u64 → L.mem s5 (P1.dnA p) ∈ T := fun h => (hD5.dn p hp).ne0 h
  have hm5 : ∀ y ∈ T, L.mem s5 (P1.affA y) = L.mem s (P1.affA y) := fun y hy => by
    rw [← haff y hy, hm _ (hal y hy).2.2, dbgRmM_af hA5 hp hc5 hpT hnT hy]
  have hW5 : DbgWFL T Cs (L.mem s5) (dbgHd (L := L) s5) lst :=
    hW.congr (fun y hy => ⟨hK.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩), hK.2 _ (Or.inl ⟨y, hy, Or.inr rfl⟩), hm5 y hy⟩)
      (fun c hc => by rw [hd5]; exact hK.2 _ (Or.inr ⟨c, hc, rfl⟩))
  have h1 := dbgRm_wf hW5 hA5 hp (by have := (hT p hp).ne0; intro e; exact this (by rw [e]; rfl)) hc5 hpT hnT
  refine h1.congr (fun y hy => ⟨hm _ (hal y hy).1, hm _ (hal y hy).2.1, hm _ (hal y hy).2.2⟩)
    (fun c hc => by
      rw [dbgHd_of_ksb hkr]
      exact hm _ (P1.nodeAt_aligned (hN5 c hc) (by simp [P1.debug_val]) (by simp [P1.debug_val])))

end Thr


section ThrJ
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

/-- **A finalisation with no work keeps the state** (DelObj's `fin_idle`:
a non-final cap, an unmapped frame, an unowned IO port). -/
theorem fin_idle_dbg [P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit) {c : capability.Cap}
    (hk : FinObjKind c) (b : Bool) (hn : ¬ FinWork c b) :
    objects.finalise_cap st arI s a c b false ⦃ r => P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.2.1 ⦄ := by
  obtain ⟨cl, he, -⟩ := fin_idle (st := st) (L := L) arI s a σ c hk b hn
  rw [he, WP.spec_ok]
  exact P1.DbgKeep.refl s

/-- **A final thread cap's finalisation at `J`, for the debug words**
(`fin_thread.dbgPre` at `J.blk`). -/
theorem JAtZ.finThreadDbgPre {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hT : P0.ArchTotal arI) {p : U64}
    (hpH : H p = some .tcb) (hna : L.actionW s ≠ p) (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) :
    objects.finalise_cap st arI s a (.Thread p) true false ⦃ r => ∃ s5 : S,
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s s5 ∧ (∀ c ∈ Cs, P1.NodePlaced st (P1.Heap.tcbs H) s5 c) ∧
      L.mem s5 (P1.affA p) ∈ Cs ∧ P1.DbgTz st (P1.Heap.tcbs H) Cs s5 ∧ L.ksb r.2.1 = L.ksb s5 ∧
      ∀ b, P1.Aligned b → L.mem r.2.1 b = dbgRmM (L.mem s5) (dbgHd (L := L) s5 (L.mem s5 (P1.affA p))) p b ⦄ := by
  rw [P1.fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_thread.dbgPre hT s a p true J.blk hpH hna hidle hv0) fun _ h => h rfl

/-- **The debug lists after a thread's finalisation at `J`**: `JAtZ` before
and after (at the same TCBs and core) keep every affinity (`SchedCore.aff`:
all the current core), so `dbgWF_thread` applies. -/
theorem JAtZ.dbgWF_thread {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {Z' : XSets} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {r s5 : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (J' : JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r a' σ') (hZT : Z'.T = Z.T) (hZc : Z'.c = Z.c)
    {p : U64} {lst : U64 → List U64} (hW : DbgWFL (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s) lst)
    (hpH : H p = some .tcb)
    (hpre : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s5 ∧ (∀ c ∈ Cs, P1.NodePlaced st (P1.Heap.tcbs H) s5 c) ∧
      L.mem s5 (P1.affA p) ∈ Cs ∧ P1.DbgTz st (P1.Heap.tcbs H) Cs s5 ∧ L.ksb r = L.ksb s5 ∧
      ∀ b, P1.Aligned b → L.mem r b = dbgRmM (L.mem s5) (dbgHd (L := L) s5 (L.mem s5 (P1.affA p))) p b) :
    DbgWFL (P1.Heap.tcbs H) Cs (L.mem r) (dbgHd (L := L) r) (fun c => (lst c).erase p) := by
  obtain ⟨hK, hN5, hc5, hD5, hkr, hm⟩ := hpre
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  obtain ⟨Q0, R0, hc0, -⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q1, R1, hc1, -⟩ := J'.xtop.fin.1.1.1.lists
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  refine Fl4Proofs.P3.dbgWF_thread hq.tcbs hW hK hN5 hpH hc5 hD5 hkr hm fun y hy => ?_
  rw [hc1.aff y (by rw [hZT, hTe]; exact hy), hc0.aff y (by rw [hTe]; exact hy), hZc]

end ThrJ

end

end Fl4Proofs.P3
