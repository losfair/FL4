/-
P3 (DESIGN.md §9), scheduling contexts: **`JAtZ` across an SC step**
(`JAtZ.sc_frame`): FL4's writes in the SC code's footprint (`TFoot`) and the
spec's `ScTKw` step keep the fields no SC step touches, given the ones it
re-establishes.

Kept by the frame: the kernel-global apartness (`ks`, `nk`: the base is
kept), the sets' fields (`thT`, `ip`, `zH`, `c0`, `bound`), the spec objects'
cover (`cover`, `obj`: `ScTKw` keeps every object's kind), `SpecFree` (the
caps and the objects' sizes kept), and the CSpace invariants (`del`, `ut`,
`finM`: no slot word is in `TFoot`, `SlotsSame`).

Re-established by the step (premises): `XTopAt`, the call stacks, yield,
MCP, buffer words, `RPlaced`, `SlotsApart`, `JPlaced`, the dead set, the
kernel-global words (`JKern`), the untyped caps' facts, the scheduler
invariants and P1's `BlkOK`.
-/
import Fl4Proofs.P3.JointAt
import Fl4Proofs.P3.SchedValidLinks
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

theorem Sched.ScTKw.ksz {P : ObjRef → Prop} {σ σ' : State Unit} (hK : Sched.ScTKw P σ σ') : KSz σ σ' := by
  intro o ko' ho
  have hk := hK.kh o
  rw [ho] at hk
  cases h0 : σ.kheap o with
  | none => rw [h0] at hk; exact hk.elim
  | some ko =>
    rw [h0] at hk
    refine ⟨ko, rfl, ?_⟩
    rcases hk with e | ⟨x, y, e1, e2, -⟩ | ⟨x, y, n, e1, e2⟩ | ⟨x, y, e1, e2, -⟩ | ⟨x, y, e1, e2, -⟩
    · rw [e]
    all_goals (subst e1; subst e2; rfl)

theorem Sched.ScTKw.kind_back {P : ObjRef → Prop} {σ σ' : State Unit} (hK : Sched.ScTKw P σ σ') {o : ObjRef}
    {ko' : KernelObject} (ho : σ'.kheap o = some ko') :
    ∃ ko, σ.kheap o = some ko ∧ ((∃ x, ko' = .notification x) → ∃ x, ko = .notification x) ∧
      ((∃ x, ko' = .endpoint x) → ∃ x, ko = .endpoint x) ∧ ((∃ x, ko' = .reply x) → ∃ x, ko = .reply x) ∧
      ((∃ x, ko' = .tcb x) → ∃ x, ko = .tcb x) ∧ ((∃ x n, ko' = .schedContext x n) → ∃ x n, ko = .schedContext x n) := by
  have hk := hK.kh o
  rw [ho] at hk
  cases h0 : σ.kheap o with
  | none => rw [h0] at hk; exact hk.elim
  | some ko =>
    rw [h0] at hk
    refine ⟨ko, rfl, ?_⟩
    rcases hk with e | ⟨x, y, e1, e2, -⟩ | ⟨x, y, n, e1, e2⟩ | ⟨x, y, e1, e2, -⟩ | ⟨x, y, e1, e2, -⟩
    · subst e; exact ⟨id, id, id, id, id⟩
    all_goals (subst e1; subst e2; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all)

/-- The SC code's spec step keeps the arch objects. -/
theorem Sched.ScTKw.arch_back {P : ObjRef → Prop} {σ σ' : State Unit} (hK : Sched.ScTKw P σ σ') {o : ObjRef}
    {ao : ArchKernelObj} (ho : σ'.kheap o = some (.archObj ao)) : σ.kheap o = some (.archObj ao) := by
  have hk := hK.kh o
  rw [ho] at hk
  cases h0 : σ.kheap o with
  | none => rw [h0] at hk; exact hk.elim
  | some ko =>
    rw [h0] at hk
    rcases hk with e | ⟨x, y, -, e2, -⟩ | ⟨x, y, n, -, e2⟩ | ⟨x, y, -, e2, -⟩ | ⟨x, y, -, e2, -⟩
    · rw [e]
    all_goals cases e2

theorem Sched.SpecCover.tkw {H : P1.Heap} {P : ObjRef → Prop} {σ σ' : State Unit} (h : Sched.SpecCover H σ)
    (hK : Sched.ScTKw P σ σ') : Sched.SpecCover H σ' := by
  refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun y k ho => ?_,
    fun o ao ho => h.arch o ao (hK.arch_back ho)⟩
  · obtain ⟨ko, hk, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ntfn o x0 hk
  · obtain ⟨ko, hk, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ep o x0 hk
  · obtain ⟨ko, hk, -, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.reply o x0 hk
  · obtain ⟨ko, hk, -, -, -, -, h1⟩ := hK.kind_back ho
    obtain ⟨y0, k0, rfl⟩ := h1 ⟨y, k, rfl⟩; exact h.sc0 y0 k0 hk

theorem Sched.ObjCover.tkw {N T E R C : Set U64} {P : ObjRef → Prop} {σ σ' : State Unit}
    (h : Sched.ObjCover N T E R C σ) (hK : Sched.ScTKw P σ σ') : Sched.ObjCover N T E R C σ' := by
  refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o y k ho => ?_⟩
  · obtain ⟨ko, hk, -, -, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.tcb o x0 hk
  · obtain ⟨ko, hk, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ntfn o x0 hk
  · obtain ⟨ko, hk, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ep o x0 hk
  · obtain ⟨ko, hk, -, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.reply o x0 hk
  · obtain ⟨ko, hk, -, -, -, -, h1⟩ := hK.kind_back ho
    obtain ⟨y0, k0, rfl⟩ := h1 ⟨y, k, rfl⟩; exact h.sc o y0 k0 hk

theorem Sched.ScTKw.ntfn' {P : ObjRef → Prop} {σ σ' : State Unit} (h : Sched.ScTKw P σ σ') {p : ObjRef}
    {x : Notification} (hk : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ y.ntfnObj = x.ntfnObj ∧ y.ntfnBoundTcb = x.ntfnBoundTcb := by
  have := h.kh p
  rw [hk] at this
  cases e : σ'.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o =>
    rw [e] at this
    rcases this with rfl | ⟨_, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨x1, y, e1, rfl, hy⟩ | ⟨_, _, e1, -⟩
    · exact ⟨x, rfl, rfl, rfl⟩
    all_goals (try cases e1)
    refine ⟨y, rfl, ?_, ?_⟩
    · rw [hy]
    · rw [hy]

/-- The SC code's spec step keeps every priority (`TcbSchedOnly`). -/
theorem Sched.ScTKw.prioOf {P : ObjRef → Prop} {σ σ' : State Unit} (h : Sched.ScTKw P σ σ') (u : ObjRef) :
    Sched.prioOf σ' u = Sched.prioOf σ u := by
  unfold Sched.prioOf; rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq]
  have := h.kh u
  revert this
  cases σ.kheap u <;> cases σ'.kheap u <;> simp only [Sched.OTK, imp_self, IsEmpty.forall_iff]
  rename_i a b
  rintro (rfl | ⟨x, y, rfl, rfl, hso, -⟩ | ⟨x, y, n, rfl, rfl⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩)
  · rfl
  · simp only [Option.map_some, Option.getD_some]; rw [hso]
  all_goals rfl

/-- **The SC code's spec step keeps the IPC queues sorted**: endpoints kept,
notifications' queues kept, priorities kept. -/
theorem Sched.IpcSorted.tkw {P : ObjRef → Prop} {σ σ' : State Unit} (h : Sched.IpcSorted σ)
    (hK : Sched.ScTKw P σ σ') : Sched.IpcSorted σ' := by
  refine h.frame (fun p x' hk => ?_) (fun p x' hk => ?_) hK.prioOf
  · obtain ⟨ko, hk0, -, h1, -⟩ := hK.kind_back hk
    obtain ⟨x0, rfl⟩ := h1 ⟨x', rfl⟩
    rw [hK.ep hk0] at hk; cases hk
    exact ⟨_, hk0, rfl⟩
  · obtain ⟨ko, hk0, h1, -⟩ := hK.kind_back hk
    obtain ⟨x0, rfl⟩ := h1 ⟨x', rfl⟩
    obtain ⟨y, hy, ho, -⟩ := hK.ntfn' hk0
    rw [hk] at hy; cases hy
    exact ⟨_, hk0, by rw [ho]⟩

end Spec

theorem FinM.of_capV {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G)
    (hc : ∀ x ∈ G.chains.flatten, capV mem' x = capV mem x) : FinM mem' G := by
  have hc' : ∀ ch ∈ G.chains, ∀ x ∈ ch, capV mem' x = capV mem x := fun ch hch x hx =>
    hc x (List.mem_flatten.2 ⟨ch, hch, hx⟩)
  refine ⟨fun ch1 h1 ch2 h2 x hx y hy ho => ?_, fun x hx y hy hne ho h1 h2 h3 => ?_,
    fun x hx y hy hne h1 h2 h3 => ?_, fun x hx y hy hne h1 => ?_⟩
  · rw [hc' ch1 h1 x hx, hc' ch2 h2 y hy] at ho; exact hF.conn ch1 h1 ch2 h2 x hx y hy ho
  · simp only [hc x hx, hc y hy] at ho h1 h2 h3 ⊢; exact hF.key x hx y hy hne ho h1 h2 h3
  · unfold srM at h3; simp only [hc x hx, hc y hy] at h1 h2 h3 ⊢; exact hF.fnest x hx y hy hne h1 h2 h3
  · simp only [hc x hx, hc y hy] at h1 ⊢; exact hF.zfin x hx y hy hne h1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`SchedValid` by the rebuild** (`schedValid_of_blk`): from `XTopAt`,
the sets being `H`'s TCBs and replies, `ObjCover`, P1's `BlkOK`, `H`'s
endpoints and notifications in the sets, the call stacks, yield, `Inv` and
the spec's links. -/
theorem schedValid_rebuild {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ)
    (hTe : Z.T = P1.Heap.tcbs H) (hRe : Z.R = P1.Heap.replies H) (hCv : Sched.ObjCover Z.N Z.T Z.E Z.R Z.C σ)
    (hB : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s)
    (hE : ∀ e, H e = some .ep → e ∈ Z.E) (hN : ∀ n, H n = some .ntfn → n ∈ Z.N)
    (hCR : Sched.CallRel (L.mem s) Z.R Z.C σ Lst) (hY : Sched.YieldRel Z.T Z.C (L.mem s) σ)
    (hC0 : ∀ q ∈ Z.C, q ≠ 0#u64) (hInv : Sched.Inv σ) (hSL : Sched.ScLinkHyp σ) : Sched.SchedValid σ := by
  have hI := hX.ipc
  rw [hTe, hRe] at hI hCv
  rw [hRe] at hCR
  rw [hTe] at hY
  exact Sched.schedValid_of_blk hB hI hCv hE hN hCR hY hC0 (Sched.epRdyHyp_of hI hCv hInv) hSL

/-- **`ScLinkHyp` by the rebuild** (`scLinkHyp_of`): from `XTopAt` (the IPC
relation's TCBs and notifications, the SC relation's `TCB`, `NTFN` and
`SPORADIC` words), the sets' TCBs being `H`'s, `ObjCover`, P1's `BlkOK`
(`ScExtra0`: the words name `H`'s TCBs and notifications), `H`'s
notifications in the set, `JPlaced` (the SCs are `H`'s) and no null SC. So
no step owes the spec's links: they follow from the relation and P1's
invariant at the post. -/
theorem scLink_rebuild {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ)
    (hTe : Z.T = P1.Heap.tcbs H) (hCv : Sched.ObjCover Z.N Z.T Z.E Z.R Z.C σ)
    (hB : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s)
    (hN : ∀ n, H n = some .ntfn → n ∈ Z.N) (hjpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s σ)
    (hC0 : ∀ q ∈ Z.C, q ≠ 0#u64) : Sched.ScLinkHyp σ := by
  have hI := hX.ipc
  obtain ⟨Q, R, -, hs⟩ := hX.fin.1.1.1.lists
  obtain ⟨Tr, Cq, hJ⟩ := hjpl
  obtain ⟨-, -, hXi, -, -⟩ := hB
  rw [hTe] at hI hCv
  refine Sched.scLinkHyp_of hI hCv hs.scs (fun c hc => ?_) hXi.2.2.toScExtra0 fun n hn => hN n hn
  obtain ⟨x, n, hk, -⟩ := hs.scs c hc
  exact ⟨_, (hJ.sc c x n (hC0 c hc) hk).2⟩

/-- The sets' TCBs and replies are `H`'s. -/
theorem JAtZ.tcbs_eq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : Z.T = P1.Heap.tcbs H ∧ Z.R = P1.Heap.replies H := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact ⟨Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩,
    Set.ext fun r => ⟨fun h => J.zH.2.2.1 r h, fun h => J.hset.2.2 r h⟩⟩

/-- `VKeep` across a `TFoot` step, from the scheduler relation alone (for
`JAtZ` / `JAtZR` alike). -/
theorem VKeep.of_tfoot {th : TypedHeap} {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (hth : ∀ t, th t = some .tcb → t ∈ T)
    (hw : P1.WritesIn st s s' (Sched.TFoot st T N C c s σ)) : VKeep (L := L) th s s' :=
  VKeep.of_writes hS.placed.tcb hth hw fun b hb u hu => by
    rcases hb with hb | ⟨y, hy, rfl⟩
    · exact Sched.KFoot.ne_vcpu hS hb hu
    · exact Sched.tVcpuA_ne (K := 3472) hS.placed.tcb hy hu (Sched.yieldA_val hS.placed.tcb hy) (by omega) (by omega)

/-- **A `TFoot` step keeps every TCB's VCPU word** (KENTRY-PLAN g2b): the
scheduler's offsets (`KFoot.ne_vcpu`) and the `YIELD_TO` words (3472). -/
theorem JAtZ.tfoot_vkeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) : VKeep (L := L) Z.th s s' :=
  VKeep.of_tfoot J.xtop.fin.1.1.1 J.thT hw

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` across an SC step** (module docstring). -/
theorem JAtZ.sc_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hX : XTopAt (L := L) AR Z s' a' σ')
    (hcall : Sched.CallRel (L.mem s') Z.R Z.C σ' Lst') (hrf : Sched.RFree (L.mem s') Z.R Z.C σ' Lst')
    (hyl : Sched.YieldRel Z.T Z.C (L.mem s') σ') (hmcp : Sched.McpRel Z.T (L.mem s') σ')
    (hbuf : BufWordRel Z.T (L.mem s') σ')
    (hrp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ') (hap : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ')
    (hjpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ') (hjc : Sched.JCovD (L := L) Z.th H Z.G D' Cs s')
    (hkern : JKern (L := L) H Cs D' Z.th s' σ')
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi)
    (hnsc : Sched.NSC Z.N Z.C σ') (hinv : Sched.Inv σ') (hcur : σ'.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ')
    (hown : Sched.CurOwnW Z.T Z.C σ') (hoff : Sched.OffOK σ')
    (hact : Sched.ActIdle σ') (hbsa : Sched.BlockedScActive σ') (hcr : CurRunM σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hidl : L.idleW s' = L.idleW s) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl' : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (J.obj.tkw hK) hblk J.hset.2.1 hjpl J.c0
  have hsv : Sched.SchedValid σ' := schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (J.obj.tkw hK) hblk J.hset.1
    J.hset.2.1 hcall hyl J.c0 hinv hsl
  refine ⟨hX, hcall, hrf,
    J.rrecv.frame (Sched.TFoot.keep J.xtop.fin.1.1.1 J.rp hw).2.2 (Sched.KhRB.of_sctkw hK), hyl, hmcp, hbuf,
    by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, hrp, hap,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, hjpl, J.cover.tkw hK, J.obj.tkw hK, J.zH, ?_, J.hset, J.hscC, hjc, hkern,
    J.del.of_same hSS, UtInv.of_same hM J.ut hSS, J.bound, fun G hG => ?_, hutc, hnsc, hinv, hcur, hown, hoff, hact,
    J.c0, hbsa, hsv, J.isorted.tkw hK, hsl, hcr, hblk, by rw [hks]; exact J.intL,
    J.vsc.of_eq fun y hy => hSS.capV hy,
    J.bok.keep (IpcFrKeep.of_otk hK.kh), J.fcov.ipcFr (IpcFrKeep.of_otk hK.kh),
    J.fcap.keepU (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (IpcFrKeep.of_otk hK.kh).page, J.ext.ss hSS (J.tfoot_vkeep hw),
    J.liveX hX rfl rfl rfl hSS hKd hK.orig hidl (fun p hp => hjc.dead p (hDD p hp)), J.zDX hSS hDD⟩
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', ?_, le_rfl⟩) hK.ksz
    rw [← hSS.capV (hsl' x' hx')]; exact hc
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)

end

end

end Fl4Proofs.P3
