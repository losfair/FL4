/-
P3 (DESIGN.md §9), VSpace: **the other subsystems' relations across the
VSpace code** (the `SR` stabilities of the Vs hypothesis structures).

`OthersRel`: the scheduler, endpoint, notification, IRQ and IO-port
relations, the kernel root word (`KRootRel`), and an arch relation `AR`
between FL4's arch state and the spec's CR3 (VsArch: `ArchRefines`). `TopSR` adds the placement `TopPlaced`: the words the
other relations read lie in their objects (`OObj`: the core's node, the
low kernel-state block, the TCB fields, the endpoints, replies,
notifications, SCs and IPC-buffer words), and these are disjoint from the
objects the VSpace code writes (`VObj`: CNodes, TCB cap slots, ASID pools,
page tables and the ASID table) — l4v's object non-overlap; and the core's
node holds no endpoint-relation word (`nodeE`, for `set_thread_state`'s
action word: VsSubTop's `restart_top`).

* `TopSR.step`: the relations carry over a step whose memory writes are in
  the VSpace objects or a region outside the other objects, and whose spec
  change is an `OStep` (VsMakePoolRel: the other subsystems' fields kept;
  heap changes only at CNodes, arch objects and free cells, or in a region
  holding none of the other objects), the IPC-buffer bytes kept;
  the frames of each relation (`SchedRel.memFrame` / `.specFrame`, and the
  endpoint, notification, IRQ and IO-port ones).
* the stabilities, in the shape of the hypothesis fields (`SR := TopSR`): `capStable_top`, `ptStable_top`, `pdStable_top`,
  `pdptStable_top`, `pml4Stable_top`, `vsStable_top`, and `mpSR_top`
  (`VsMpHyps.mpSR` with `RegOK := RegOKTop`).
-/
import Fl4Proofs.P3.VsTcb
import Fl4Proofs.P3.VsMakePoolRel
import Fl4Proofs.P3.SchedRel
import Fl4Proofs.P3.IoBitmap
import Fl4Proofs.P3.IntRel
import Fl4Proofs.P3.IoPortDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section Defs
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The objects whose words the other subsystems' relations read. -/
def OObj (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S) (σ : Fl4Spec.State Unit)
    (a : U64) : Prop :=
  (L.nodeBase s c ≤ a.val ∧ a.val < L.nodeBase s c + 4288) ∨
  ((L.ksb s).val ≤ a.val ∧ a.val < (L.ksb s).val + 13568) ∨
  (∃ t ∈ T, t.val + 256 ≤ a.val ∧ a.val < t.val + 4096) ∨
  (∃ e ∈ E, e.val ≤ a.val ∧ a.val < e.val + 16) ∨
  (∃ r ∈ R, r.val ≤ a.val ∧ a.val < r.val + 32) ∨
  (∃ n ∈ N, n.val ≤ a.val ∧ a.val < n.val + 64) ∨
  (∃ sc ∈ C, ∃ x n, σ.kheap sc.bv = some (.schedContext x n) ∧ Sched.ScObj sc n a) ∨
  (∃ wp ∈ B, wp.1.val ≤ a.val ∧ a.val < wp.1.val + 8)

/-- The objects the VSpace code writes. -/
def VObj (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (ksb a : U64) : Prop :=
  (∃ q r, th q = some (.cnode r) ∧ q.val ≤ a.val ∧ a.val < q.val + 32 * 2 ^ r) ∨
  (∃ t, th t = some .tcb ∧ t.val ≤ a.val ∧ a.val < t.val + 192) ∨
  (∃ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) ∧ q.val ≤ a.val ∧ a.val < q.val + 4096) ∨
  (ksb.val + 288000 ≤ a.val ∧ a.val < ksb.val + 288000 + 16384)

/-- The placement the stabilities need (see the module docstring). -/
structure TopPlaced (th : TypedHeap) (P L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  ep : Endp.EPlaced T E R B
  vs : VsPlaced P (L.ksb s)
  pt : PtPlaced L4 L3 L2 L1
  pl : Placed th
  disj : ∀ a, OObj st N T C E R B c s σ a → ¬ VObj th P L4 L3 L2 L1 (L.ksb s) a
  /-- The core's node holds no endpoint-relation word (the scheduler action
  word that `set_thread_state` may write). -/
  nodeE : ∀ a : U64, L.nodeBase s c ≤ a.val → a.val < L.nodeBase s c + 4288 → ¬ Endp.EFoot T E R B a
  /-- The VSpace placement: the page-table words are outside the objects (so
  neither slot words nor ASID-table or pool words), and the ASID-table and
  pool words are outside the objects. -/
  po : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b
  ps : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b
  pv : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b
  vo : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b
  sd : VsSlotsDisj th P (L.ksb s)
  /-- The TCBs of the typed heap lie apart from the kernel-global area (the
  VSpace footprint's TCB state words outside the domain schedule's). -/
  tko : ∀ t, th t = some .tcb → t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val

/-- FL4's kernel root word (`ks::KERNEL_ROOT`) gives the spec's global
address space. -/
def KRootRel (m : U64 → U64) (ksb : U64) (σ : Fl4Spec.State Unit) : Prop :=
  Fl4Spec.makeCr3 (Fl4Spec.addrFromPPtr (m (core.num.U64.wrapping_add ksb layout.ks.KERNEL_ROOT)).bv) 0 = globCr3 σ

/-- The other subsystems' relations, the kernel root, and the arch relation
`AR` between FL4's arch state and the spec's CR3. -/
def OthersRel {A : Type} (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64)
    (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  Sched.SchedRel st N T C c s σ ∧ Endp.EpStateRel T E R B (L.mem s) σ ∧ Notif.NtfnStateRel N T (L.mem s) σ ∧
    IrqRel (L.mem s) (L.ksb s) σ ∧ IoRel (L.mem s) (L.ksb s) σ ∧ KRootRel (L.mem s) (L.ksb s) σ ∧
    AR a σ.archState.x64CurrentCr3

/-- **The composite `SR`** of the VSpace hypothesis structures. -/
def TopSR {A : Type} (th : TypedHeap) (P L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (c : U64) (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  OthersRel st N T C E R B c AR s a σ ∧ TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ

end Defs



/-! ## Memory frames: the other relations read only their objects -/

section MemFrame
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem tcb_oobj {s : S} {σ : Fl4Spec.State Unit} {t K : U64} (ht : t ∈ T) (hta : TcbAddr t) (h1 : 256 ≤ K.val)
    (h2 : K.val < 4096) : OObj st N T C E R B c s σ (core.num.U64.wrapping_add t K) := by
  right; right; left
  exact ⟨t, ht, by rw [Notif.tfield_val hta h2]; omega, by rw [Notif.tfield_val hta h2]; omega⟩

/-- **The scheduler relation reads only the other objects** (memory side). -/
theorem SchedRel.memFrame {s s' : S} {σ : Fl4Spec.State Unit} (hS : Sched.SchedRel st N T C c s σ)
    (hksb : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s) (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64)
    (hka : (L.ksb s).val % 8 = 0)
    (hm : ∀ b, Aligned b → OObj st N T C E R B c s σ b → L.mem s' b = L.mem s b) :
    Sched.SchedRel st N T C c s' σ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => hm _ (nodeAt_aligned hN ho h8) (Or.inl (by rw [nodeAt_val hN ho]; omega))
  have hks : ∀ K : U64, 0 < K.val → K.val < 13568 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add (L.ksb s) K) = L.mem s (core.num.U64.wrapping_add (L.ksb s) K) := by
    intro K h0 h1 h8
    have hv : (core.num.U64.wrapping_add (L.ksb s) K).val = (L.ksb s).val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    exact hm _ (by unfold Aligned; rw [hv]; omega) (Or.inr (Or.inl (by rw [hv]; omega)))
  have ha : Sched.SAgree st T C c s s' := by
    refine ⟨hksb, hcpu, fun o ho h8 _ _ => hnode o ho h8, fun y hy K hK => ?_, hks 8#u64 (by decide) (by decide)
      (by decide), hks 16#u64 (by decide) (by decide) (by decide), fun sc hsc a hal hin => ?_⟩
    · obtain ⟨h1, h2, -⟩ := Sched.schedField_ok hK
      have hya := hc.tcbs y hy
      have h3 : 256 ≤ K.val := by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      exact hm _ (field_aligned hya h1 h2) (tcb_oobj hy hya h3 h1)
    · obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
      exact hm a hal (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hk, hx.in_obj hin⟩)))))))
  have hact : Sched.nodeW st s' c layout.node.SCHED_ACTION = Sched.nodeW st s c layout.node.SCHED_ACTION := by
    unfold Sched.nodeW; rw [Sched.nodeAt_ksb hksb]
    exact hnode _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have hrp : Sched.nodeW st s' c layout.node.REPROGRAM = Sched.nodeW st s c layout.node.REPROGRAM := by
    unfold Sched.nodeW; rw [Sched.nodeAt_ksb hksb]
    exact hnode _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  refine ⟨hS.placed, fun o ho => by rw [Sched.nodeAt_ksb ha.ksb]; exact hS.nodeNW o ho,
    by rw [Sched.curDomA_ksb ha.ksb]; exact hS.domNW, by rw [Sched.dtA_ksb ha.ksb]; exact hS.dtNW,
    Sched.scOut_transfer ha.ksb (Sched.SzKeep.of_kheap rfl) hS.scOut, hS.scDisj, by rw [hact]; exact hS.actW,
    by rw [hact]; exact hS.act, by rw [hrp]; exact hS.repr, hs.core_eq ha.sc hS.core, Q, R0, hc.agree ha.toC,
    hs.agree ha⟩


theorem EpStateRel.memFrame {m m' : U64 → U64} {s : S} {σ : Fl4Spec.State Unit}
    (hR : Endp.EpStateRel T E R B m σ) (hP : Endp.EPlaced T E R B)
    (hm : ∀ b, Aligned b → OObj st N T C E R B c s σ b → m' b = m b) : Endp.EpStateRel T E R B m' σ := by
  refine Endp.EpStateRel.frame hR hP (fun a ha hf => hm a ha ?_) (Endp.KView.refl σ)
  rcases hf with ⟨e, he, h | h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, ⟨h1, h2⟩ | h⟩ | ⟨wp, hw, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩))))
  · refine Or.inr (Or.inr (Or.inl ⟨t, ht, ?_, ?_⟩)) <;> unfold Endp.TOffN at h2 <;> omega
  · refine Or.inr (Or.inr (Or.inl ⟨t, ht, ?_, ?_⟩)) <;> unfold Endp.TL at h <;> omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩))))))

theorem NtfnStateRel.memFrame {m m' : U64 → U64} {s : S} {σ : Fl4Spec.State Unit}
    (hR : Notif.NtfnStateRel N T m σ) (hP : Notif.NPlaced T N)
    (hm : ∀ b, Aligned b → OObj st N T C E R B c s σ b → m' b = m b) : Notif.NtfnStateRel N T m' σ := by
  refine Notif.NtfnStateRel.frame hR hP (fun a ha hf => hm a ha ?_) (Notif.KView.refl σ)
  rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h | h | h | h | h | h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, by omega⟩)))))
  all_goals
    subst h
    have hta := hP.tcb t ht
    first
      | (rw [Notif.tStA_eq]; exact tcb_oobj ht hta (by simp) (by simp))
      | (rw [Notif.tBlockA_eq]; exact tcb_oobj ht hta (by simp) (by simp))
      | (rw [Notif.badgeRegA_eq]; exact tcb_oobj ht hta (by simp) (by simp))
      | (rw [Notif.prioA_eq']; exact tcb_oobj ht hta (by simp) (by simp))
      | (rw [Notif.nextEp_eq]; exact tcb_oobj ht hta (by simp) (by simp))
      | (rw [Notif.prevEp_eq]; exact tcb_oobj ht hta (by simp) (by simp))

theorem IrqRel.memFrame {m m' : U64 → U64} {s : S} {σ : Fl4Spec.State Unit} (hR : IrqRel m (L.ksb s) σ)
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hm : ∀ b, Aligned b → OObj st N T C E R B c s σ b → m' b = m b) : IrqRel m' (L.ksb s) σ := by
  refine ⟨fun i hi => ?_, hR.node⟩
  have hv := irqStA_val hkf hi
  rw [hm _ (by unfold Aligned; rw [hv]; omega) (Or.inr (Or.inl (by rw [hv]; omega)))]
  exact hR.st i hi

theorem IoRel.memFrame {m m' : U64 → U64} {s : S} {σ : Fl4Spec.State Unit} (hR : IoRel m (L.ksb s) σ)
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hm : ∀ b, Aligned b → OObj st N T C E R B c s σ b → m' b = m b) : IoRel m' (L.ksb s) σ := by
  intro p hp
  have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
  have hv := ioA_val hkf hw
  unfold bitOf
  rw [hm _ (by unfold Aligned; rw [hv]; omega) (Or.inr (Or.inl (by rw [hv]; omega)))]
  exact hR p hp

end MemFrame


/-! ## Spec frames: the other relations read only their objects and fields -/

section SpecFrame
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem SchedRel.specFrame {Rg : Fl4Spec.ObjRef → Prop} {s : S} {σ σ' : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (hO : OStep Rg σ σ') (hT : ∀ t ∈ T, ¬ Rg t.bv)
    (hC : ∀ sc ∈ C, ¬ Rg sc.bv) : Sched.SchedRel st N T C c s σ' := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hz : Sched.SzKeep σ σ' := fun p x n hp => ⟨x, by rw [← hO.keep' (by rw [hp]; exact passive_sc)]; exact hp⟩
  refine ⟨hS.placed, hS.nodeNW, hS.domNW, hS.dtNW, Sched.scOut_transfer rfl hz hS.scOut,
    Sched.scDisj_transfer hz hS.scDisj, hS.actW, by rw [hO.act]; exact hS.act,
    by rw [hO.repr]; exact hS.repr, hS.core, Q, R0, hc, ?_⟩
  refine ⟨fun p hp => by rw [hO.rq]; exact hs.rq p hp, fun d p hd => by rw [hO.rq]; exact hs.rqDom d p hd,
    by rw [hO.rel]; exact hs.rel, by rw [hO.ct]; exact hs.curThread, by rw [hO.csc]; exact hs.curSc,
    by rw [hO.ctime]; exact hs.curTime, by rw [hO.cons]; exact hs.consumed, by rw [hO.cdom]; exact hs.curDom,
    fun t ht => ?_, hs.scMem, fun sc hsc => ?_, hs.idleSc, by rw [hO.dtime]; exact hs.domTime,
    by rw [hO.idle]; exact hs.idleTh⟩
  · obtain ⟨x, hk, h1⟩ := hs.tcb t ht
    exact ⟨x, by rw [hO.keep (hT t ht) (by rw [hk]; exact passive_tcb)]; exact hk, h1⟩
  · obtain ⟨x, n, hk, e⟩ := hs.scs sc hsc
    exact ⟨x, n, by rw [hO.keep (hC sc hsc) (by rw [hk]; exact passive_sc)]; exact hk, e⟩

theorem EpStateRel.specFrame {Rg : Fl4Spec.ObjRef → Prop} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (hR : Endp.EpStateRel T E R B m σ) (hO : OStep Rg σ σ') (hT : ∀ t ∈ T, ¬ Rg t.bv)
    (hE : ∀ e ∈ E, ¬ Rg e.bv) (hRR : ∀ r ∈ R, ¬ Rg r.bv)
    (hB : ∀ wp ∈ B, Endp.loadWordAt σ'.machineState.underlyingMemory wp.2 =
      Endp.loadWordAt σ.machineState.underlyingMemory wp.2) : Endp.EpStateRel T E R B m σ' := by
  refine ⟨fun e he => ?_, fun r hr => ?_, fun t ht => ?_, fun wp hw => by rw [hB wp hw]; exact hR.buf wp hw⟩
  · obtain ⟨x, hk, h1⟩ := hR.ep e he
    exact ⟨x, by rw [hO.keep (hE e he) (by rw [hk]; exact passive_ep)]; exact hk, h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.reply r hr
    exact ⟨x, by rw [hO.keep (hRR r hr) (by rw [hk]; exact passive_reply)]; exact hk, h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    exact ⟨x, by rw [hO.keep (hT t ht) (by rw [hk]; exact passive_tcb)]; exact hk, h1⟩

theorem NtfnStateRel.specFrame {Rg : Fl4Spec.ObjRef → Prop} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (hR : Notif.NtfnStateRel N T m σ) (hO : OStep Rg σ σ') (hT : ∀ t ∈ T, ¬ Rg t.bv)
    (hN : ∀ n ∈ N, ¬ Rg n.bv) : Notif.NtfnStateRel N T m σ' := by
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hk, h1⟩ := hR.ntfn n hn
    exact ⟨x, by rw [hO.keep (hN n hn) (by rw [hk]; exact passive_ntfn)]; exact hk, h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    exact ⟨x, by rw [hO.keep (hT t ht) (by rw [hk]; exact passive_tcb)]; exact hk, h1⟩

theorem IrqRel.specFrame {Rg : Fl4Spec.ObjRef → Prop} {m : U64 → U64} {kb : U64} {σ σ' : Fl4Spec.State Unit}
    (hR : IrqRel m kb σ) (hO : OStep Rg σ σ') : IrqRel m kb σ' :=
  ⟨fun i hi => by rw [hO.ist]; exact hR.st i hi, fun i hi => by rw [hO.inode]; exact hR.node i hi⟩

theorem IoRel.specFrame {Rg : Fl4Spec.ObjRef → Prop} {m : U64 → U64} {kb : U64} {σ σ' : Fl4Spec.State Unit}
    (hR : IoRel m kb σ) (hO : OStep Rg σ σ') : IoRel m kb σ' :=
  fun p hp => by rw [hO.io]; exact hR p hp

end SpecFrame


/-! ## The step theorem -/

section Step
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem OObj.of_step {Rg : Fl4Spec.ObjRef → Prop} {s s' : S} {σ σ' : Fl4Spec.State Unit} (hksb : L.ksb s' = L.ksb s)
    (hO : OStep Rg σ σ') {a : U64} (h : OObj st N T C E R B c s' σ' a) : OObj st N T C E R B c s σ a := by
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
  unfold OObj at h ⊢
  rw [hnb, hksb] at h
  rcases h with h | h | h | h | h | h | ⟨sc, hsc, x, n, hk, ho⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, ?_, ho⟩))))))
  rw [← hO.keep' (by rw [hk]; exact passive_sc)]; exact hk

/-- **The composite relation across a VSpace step**: memory writes in the
VSpace objects or a region `Rw` outside the other objects, the spec change
an `OStep` whose region holds none of the other objects, the IPC-buffer
words kept, and the arch relation kept. -/
theorem TopSR.step {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Rg : Fl4Spec.ObjRef → Prop} {Rw : U64 → Prop}
    {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hksb : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hW : ∀ b, Aligned b → ¬ VObj th P L4 L3 L2 L1 (L.ksb s) b → ¬ Rw b → L.mem s' b = L.mem s b)
    (hRw : ∀ b, Rw b → ¬ OObj st N T C E R B c s σ b) (hO : OStep Rg σ σ')
    (hRg : ∀ q : U64, Rg q.bv → q ∉ T ∧ q ∉ E ∧ q ∉ R ∧ q ∉ N ∧ q ∉ C)
    (hB : ∀ wp ∈ B, Endp.loadWordAt σ'.machineState.underlyingMemory wp.2 =
      Endp.loadWordAt σ.machineState.underlyingMemory wp.2)
    (hAR : AR a σ.archState.x64CurrentCr3 → AR a' σ'.archState.x64CurrentCr3) :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a' σ' := by
  obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
  have hm : ∀ b, Aligned b → OObj st N T C E R B c s σ b → L.mem s' b = L.mem s b :=
    fun b hb ho => hW b hb (hP.disj b ho) (fun h => hRw b h ho)
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hT : ∀ t ∈ T, ¬ Rg t.bv := fun t ht h => (hRg t h).1 ht
  have hE : ∀ e ∈ E, ¬ Rg e.bv := fun e he h => (hRg e h).2.1 he
  have hRR : ∀ r ∈ R, ¬ Rg r.bv := fun r hr h => (hRg r h).2.2.1 hr
  have hN : ∀ n ∈ N, ¬ Rg n.bv := fun n hn h => (hRg n h).2.2.2.1 hn
  have hC : ∀ sc ∈ C, ¬ Rg sc.bv := fun sc hsc h => (hRg sc h).2.2.2.2 hsc
  refine ⟨⟨SchedRel.specFrame (SchedRel.memFrame hSch hksb hcpu hkf hka hm) hO hT hC,
    EpStateRel.specFrame (EpStateRel.memFrame hEp hP.ep hm) hO hT hE hRR hB,
    NtfnStateRel.specFrame (NtfnStateRel.memFrame hNt hSch.placed hm) hO hT hN,
    by rw [hksb]; exact IrqRel.specFrame (IrqRel.memFrame hIrq hkf hka hm) hO,
    by rw [hksb]; exact IoRel.specFrame (IoRel.memFrame hIo hkf hka hm) hO, ?_, hAR hAr⟩,
    ⟨hP.ep, by rw [hksb]; exact hP.vs, hP.pt, hP.pl, fun x hx => by
      rw [hksb]; exact hP.disj x (OObj.of_step hksb hO hx),
      fun x h1 h2 => by
        have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
        rw [hnb] at h1 h2; exact hP.nodeE x h1 h2,
      hP.po, hP.ps, by rw [hksb]; exact hP.pv, by rw [hksb]; exact hP.vo, by rw [hksb]; exact hP.sd, by rw [hksb]; exact hP.tko⟩⟩
  unfold KRootRel globCr3 at hKr ⊢
  have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
    unfold layout.ks.KERNEL_ROOT
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  rw [hksb, hm _ (by unfold Aligned; rw [hkv]; unfold layout.ks.KERNEL_ROOT at hkv; omega)
    (Or.inr (Or.inl (by rw [hkv]; omega))), hO.gpml4]
  exact hKr

end Step


/-! ## The stabilities -/

section Stable
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem slot_vobj (hP : Placed th) {a : U64} (ha : IsSlot th a) {b : U64} (h1 : a.val ≤ b.val)
    (h2 : b.val < a.val + 32) (ksb : U64) : VObj th P L4 L3 L2 L1 ksb b := by
  obtain ⟨p, i, hpi, rfl⟩ := ha
  have hv := hpi.val hP
  rcases hpi with ⟨r, hp, hi⟩ | ⟨hp, hi⟩
  · left; refine ⟨p, r, hp, by omega, ?_⟩
    have : 32 * (i + 1) ≤ 32 * 2 ^ r := Nat.mul_le_mul_left _ hi
    omega
  · right; left; refine ⟨p, hp, by omega, ?_⟩
    simp [tcbSlots] at hi; omega

theorem slotW_vobj (hP : Placed th) {b : U64} (h : SlotW th b) (ksb : U64) : VObj th P L4 L3 L2 L1 ksb b := by
  obtain ⟨x, hx, rfl | rfl⟩ := h
  · exact slot_vobj hP hx (le_refl _) (by omega) ksb
  · have hf := hx.fit hP
    exact slot_vobj hP hx (by rw [wa8_val (by omega)]; omega) (by rw [wa8_val (by omega)]; omega) ksb

theorem table_vobj (hPP : PtPlaced L4 L3 L2 L1) {q : U64} (hq : q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) {i : U64}
    (hi : i.val < 512) (ksb : U64) : VObj th P L4 L3 L2 L1 ksb (peA q i) := by
  have hv := peA_val (tbl_fit (hPP q hq)) hi
  right; right; left
  exact ⟨q, Or.inr hq, by omega, by omega⟩

theorem vsWrite_vobj (hVP : VsPlaced P ksb) {b : U64} (h : VsWrite P ksb b) : VObj th P L4 L3 L2 L1 ksb b := by
  rcases h with ⟨hi, hh, rfl⟩ | ⟨p, hp, lo, hl, rfl⟩
  · have hv := atA_val hVP.ksb_fit hh
    right; right; right; omega
  · have hv := peA_val (hVP.pal p hp).2 hl
    right; right; left
    exact ⟨p, Or.inl hp, by omega, by omega⟩

/-- A step with no region, for writes in `W ⊆ VObj`. -/
theorem TopSR.step0 {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {W : U64 → Prop}
    {s s' : S} {a : A} {σ σ' : Fl4Spec.State Unit} (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hWV : ∀ b, W b → VObj th P L4 L3 L2 L1 (L.ksb s) b) (hw : WritesIn st s s' W)
    (hO : OStep (fun _ => False) σ σ') (hum : σ'.machineState = σ.machineState)
    (hcr : σ'.archState.x64CurrentCr3 = σ.archState.x64CurrentCr3) :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' :=
  TopSR.step (Rw := fun _ => False) hS hw.1 hw.2.1 (fun b hb hv _ => hw.2.2 b hb (fun h => hv (hWV b h)))
    (fun _ h => h.elim) hO (fun _ h => h.elim) (fun wp _ => by rw [hum])
    (fun h => by rw [hcr]; exact h)

theorem capStable_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hw : WritesIn st s s' (SlotW th)) (hc : CapStep σ σ') : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  obtain ⟨p, r, cs, idx, a', hk, rfl⟩ := hc
  exact TopSR.step0 hS (fun b h => slotW_vobj hS.2.pl h _) hw (OStep.cnode hk idx a') rfl rfl

theorem ptStable_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hw : WritesIn st s s' (PtW L1)) (hc : PtStep σ σ') : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  obtain ⟨p, f, f', hk, rfl⟩ := hc
  exact TopSR.step0 hS (fun b ⟨q, hq, i, hi, e⟩ => e ▸ table_vobj hS.2.pt (Or.inr (Or.inr (Or.inr hq))) hi _)
    hw (OStep.arch (Or.inr (Or.inr ⟨_, hk⟩)) _) rfl rfl

theorem pdStable_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hw : WritesIn st s s' (PdW L2)) (hc : PdStep σ σ') : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  obtain ⟨p, f, f', hk, rfl⟩ := hc
  exact TopSR.step0 hS (fun b ⟨q, hq, i, hi, e⟩ => e ▸ table_vobj hS.2.pt (Or.inr (Or.inr (Or.inl hq))) hi _)
    hw (OStep.arch (Or.inr (Or.inr ⟨_, hk⟩)) _) rfl rfl

theorem pdptStable_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hw : WritesIn st s s' (PdptW L3)) (hc : PdptStep σ σ') :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  obtain ⟨p, f, f', hk, rfl⟩ := hc
  exact TopSR.step0 hS (fun b ⟨q, hq, i, hi, e⟩ => e ▸ table_vobj hS.2.pt (Or.inr (Or.inl hq)) hi _)
    hw (OStep.arch (Or.inr (Or.inr ⟨_, hk⟩)) _) rfl rfl

theorem pml4Stable_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hw : WritesIn st s s' (Pml4W L4)) (hc : Pml4Step σ σ') :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  obtain ⟨p, f, f', hk, rfl⟩ := hc
  exact TopSR.step0 hS (fun b ⟨q, hq, i, hi, e⟩ => e ▸ table_vobj hS.2.pt (Or.inl hq) hi _)
    hw (OStep.arch (Or.inr (Or.inr ⟨_, hk⟩)) _) rfl rfl

theorem vsStable_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hw : WritesIn st s s' (VsWrite P (L.ksb s))) (hc : VsStep σ σ') :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  rcases hc with ⟨p, f, f', hk, rfl⟩ | ⟨t, rfl⟩
  · exact TopSR.step0 hS (fun b h => vsWrite_vobj hS.2.vs h) hw (OStep.arch (Or.inr (Or.inr ⟨_, hk⟩)) _) rfl rfl
  · exact TopSR.step0 hS (fun b h => vsWrite_vobj hS.2.vs h) hw (OStep.table t) rfl rfl

end Stable


/-! ## `MakePool` -/

section MakePool
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- What the composite relation needs of `MakePool`'s frame `[p, p + 4096)`:
aligned, not wrapping, holding none of the other subsystems' objects nor an
IPC-buffer byte. -/
def RegOKTop (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S) (σ : Fl4Spec.State Unit)
    (p : U64) : Prop :=
  p.val % 4096 = 0 ∧ p.val + 4096 ≤ 2 ^ 64 ∧
    (∀ a : U64, p.val ≤ a.val → a.val < p.val + 4096 → ¬ OObj st N T C E R B c s σ a) ∧
    ∀ wp ∈ B, ∀ i ∈ Fl4Spec.intUpto 0 7, (wp.2 + (7 - BitVec.ofInt 64 i)).toNat < p.val ∨
      p.val + 4096 ≤ (wp.2 + (7 - BitVec.ofInt 64 i)).toNat

/-- **`VsMpHyps.mpSR` for the composite relation.** -/
theorem mpSR_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (p hi : U64) (hhi : hi.val < 2048)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (hRO : RegOKTop (L := L) N T C E R B c s σ p)
    (hksb : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hW : ∀ b, Aligned b → ¬ MpW th p (L.ksb s) hi b → L.mem s' b = L.mem s b) (hMp : MpStep p σ σ') :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  obtain ⟨hpal, hpfit, hro, hrb⟩ := hRO
  have hP := hS.2
  have hoq : ∀ q : U64, q.bv ∈ Fl4Proofs.P3.regionSet p.bv 12 → OObj st N T C E R B c s σ q → False :=
    fun q hq ho => by
      rw [regionSet_iff p q 12 (by decide) hpfit] at hq
      exact hro q hq.1 hq.2 ho
  refine TopSR.step (Rw := fun b => p.val ≤ b.val ∧ b.val < p.val + 4096) (Rg := fun q => q ∈ regionSet p.bv 12)
    hS hksb hcpu (fun b hb hv hr => hW b hb ?_) (fun b hb => hro b hb.1 hb.2) hMp.1 ?_ ?_ (fun h => by rw [hMp.2.2]; exact h)
  · rintro (⟨x, k, hx, hk, rfl⟩ | h | rfl)
    · have hf := hx.fit hP.pl
      have := hk.lt
      have hw := wordOf_val (a := x) (k := k) (by omega)
      exact hv (slot_vobj hP.pl hx (by rw [hw]; omega) (by rw [hw]; omega) _)
    · exact hr h
    · exact hv (vsWrite_vobj hP.vs (Or.inl ⟨hi, hhi, rfl⟩))
  · intro q hq
    refine ⟨fun hT => ?_, fun hE => hoq q hq (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hE, le_refl _, by omega⟩)))),
      fun hR => hoq q hq (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hR, le_refl _, by omega⟩))))),
      fun hN => hoq q hq (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hN, le_refl _, by omega⟩)))))),
      fun hC => ?_⟩
    · have hta := hS.1.1.placed.tcb q hT
      have hq' := (regionSet_iff p q 12 (by decide) hpfit).1 hq
      have hqp : q.val = p.val := by have := hta.align; omega
      have hfit := hta.fits
      let a : U64 := ⟨BitVec.ofNat 64 (q.val + 256)⟩
      have hav : a.val = q.val + 256 := by
        show (BitVec.ofNat 64 (q.val + 256)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hro a (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨q, hT, by omega, by omega⟩)))
    · obtain ⟨Q, R0, -, hs⟩ := hS.1.1.lists
      obtain ⟨x, n, hk, -⟩ := hs.scs q hC
      exact hoq q hq (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hC, x, n, hk, le_refl _, by have := Nat.one_le_two_pow (n := n); omega⟩)))))))
  · intro wp hw
    unfold Endp.loadWordAt
    congr 1
    apply List.map_congr_left
    intro i hi'
    exact hMp.2.1 _ (hrb wp hw i hi')


/-- `RegOKTop` reads the heap only for the SC cells. -/
theorem OObj.of_kh {s s' : S} {σ σ' : Fl4Spec.State Unit} (hksb : L.ksb s' = L.ksb s)
    (hsc : ∀ q x n, σ'.kheap q = some (.schedContext x n) → σ.kheap q = some (.schedContext x n)) {a : U64}
    (h : OObj st N T C E R B c s' σ' a) : OObj st N T C E R B c s σ a := by
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
  unfold OObj at h ⊢
  rw [hnb, hksb] at h
  rcases h with h | h | h | h | h | h | ⟨sc, hsc', x, n, hk, ho⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc', x, n, hsc _ _ _ hk, ho⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- **`RegOKTop` across `set_thread_state Restart`** (the `restart` field's
`RegOK` part, `VsMpHyps`): the kernel-state base is kept, and the spec's
`set_thread_state` changes a TCB, no SC. -/
theorem regOK_restart {s : S} {σ : Fl4Spec.State Unit} {p ct : U64} {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (h : RegOKTop (L := L) N T C E R B c s σ p) :
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' => RegOKTop (L := L) N T C E R B c s'
      (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) p ⦄ := by
  refine WP.spec_mono (set_thread_state_cpu s ct _) fun s' ⟨hk', _⟩ =>
    ⟨h.1, h.2.1, fun a h1 h2 ho => h.2.2.1 a h1 h2 (OObj.of_kh hk' (fun q y n hq => ?_) ho), h.2.2.2⟩
  rw [Notif.stsAct_kheap, Notif.updK_kheap] at hq
  by_cases e : q = ct.bv
  · subst e; rw [Function.update_self] at hq; cases hq
  · rwa [Function.update_of_ne e] at hq

end MakePool

end

end Fl4Proofs.P3.Vs
