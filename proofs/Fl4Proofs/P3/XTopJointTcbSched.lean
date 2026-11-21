/-
P3 (DESIGN.md §9), TCB: **the scheduler labels of the Thread cap at `J`**
(toward XTopJointTcb's SetMCPriority, SetPriority and SetSchedParams).

* `QKM`: XTopJointRegFrame's quiet step `QKY` with the TCBs' MCP and IPC
  buffer also changing; what it keeps (the `QKY` lemmas, but `mcpKeep` and
  `bufKeep`).
* `WideW`: the words of the TCBs of `T` (offsets 256..4096), core `c`'s node,
  the notifications of `N` and the SCs of `C` (XTopJointFinW's `finW_cases`
  as a write set); `JAtZ.wideW_scOut`, `wideW_irq`, `wideW_utc`: XTopJointFinW's
  `finW_*` for it.
* `JAtZ.mcpWrJ`: a TCB's `MCP` word written at `J` with the spec's
  `tcb_mcpriority` (`McpRel.set`), the rest as `JAtZ.reg_frameF`.
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical

noncomputable section


/-- **A quiet step with MCPs** (XTopJointRegFrame's `QKY`, the TCBs' maximum
controlled priority also allowed to change): the scheduler's abstract fields
kept; every object kept but TCBs changed in their saved context, yield-to,
fault, flags and MCP, and SCs in their consumed time and yield-from. -/
structure QKM (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  tm : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  idle : σ'.idleThread = σ.idleThread
  isc : σ'.idleSc = σ.idleSc
  act : σ'.schedulerAction = σ.schedulerAction
  rel : σ'.releaseQueue = σ.releaseQueue
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  arch : σ'.archState = σ.archState
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨
    (∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧
      y = { x with tcbArch := y.tcbArch, tcbYieldTo := y.tcbYieldTo, tcbFault := y.tcbFault, tcbFlags := y.tcbFlags, tcbMcpriority := y.tcbMcpriority, tcbIpcBuffer := y.tcbIpcBuffer }) ∨
    (∃ z w n, σ.kheap p = some (.schedContext z n) ∧ σ'.kheap p = some (.schedContext w n) ∧
      w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom })

/-- The MCP update of one TCB is a `QKM` step. -/
theorem QKM.mcp {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (m : Priority) :
    QKM σ (updK σ t (.tcb { x with tcbMcpriority := m })) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
  by_cases e1 : q = t
  · subst e1; exact Or.inr (Or.inl ⟨x, { x with tcbMcpriority := m }, hk, by simp [updK], rfl⟩)
  · exact Or.inl (by simp [updK, e1])

/-- The IPC-buffer update of one TCB is a `QKM` step. -/
theorem QKM.ipcBuf {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (b : VSpaceRef) :
    QKM σ (updK σ t (.tcb { x with tcbIpcBuffer := b })) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
  by_cases e1 : q = t
  · subst e1; exact Or.inr (Or.inl ⟨x, { x with tcbIpcBuffer := b }, hk, by simp [updK], rfl⟩)
  · exact Or.inl (by simp [updK, e1])

/-- The MCP update of one TCB keeps the IPC buffers. -/
theorem bufKeep_mcp {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (m : Priority) :
    ∀ p x', σ.kheap p = some (.tcb x') → ∃ y, (updK σ t (.tcb { x with tcbMcpriority := m })).kheap p =
      some (.tcb y) ∧ y.tcbIpcBuffer = x'.tcbIpcBuffer := fun p x' hp => by
  by_cases e : p = t
  · subst e; rw [hk] at hp; cases hp; exact ⟨{ x with tcbMcpriority := m }, by simp [updK], rfl⟩
  · exact ⟨x', by simp [updK, e, hp], rfl⟩

/-- The IPC-buffer update of one TCB keeps the MCPs. -/
theorem mcpKeep_buf {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (b : VSpaceRef) :
    McpKeep σ (updK σ t (.tcb { x with tcbIpcBuffer := b })) := fun p x' hp => by
  by_cases e : p = t
  · subst e; rw [hk] at hp; cases hp; exact ⟨{ x with tcbIpcBuffer := b }, by simp [updK], rfl⟩
  · exact ⟨x', by simp [updK, e, hp], rfl⟩

section
variable {σ σ' : State Unit} (h : QKM σ σ')
include h

/-- No reply bound to a receiver gained (`ScRecvLinks`' `KhRB`). -/
theorem QKM.khrb : KhRB σ σ' := by
  intro p o' hp
  rcases h.kh p with e | ⟨x, y, h1, h2, e⟩ | ⟨z, w, n, h1, h2, -⟩
  · exact ⟨o', by rw [← e]; exact hp, ObjRB.refl o'⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.tcb (Or.inl (by rw [e]))⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)⟩

theorem QKM.tcb {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ y = { x with tcbArch := y.tcbArch, tcbYieldTo := y.tcbYieldTo, tcbFault := y.tcbFault, tcbFlags := y.tcbFlags, tcbMcpriority := y.tcbMcpriority, tcbIpcBuffer := y.tcbIpcBuffer } := by
  rcases h.kh p with e | ⟨a, b, ha, hb, e⟩ | ⟨z, w, n, ha, -, -⟩
  · exact ⟨x, e.trans hk, rfl⟩
  · rw [hk] at ha; cases ha; exact ⟨b, hb, e⟩
  · rw [hk] at ha; cases ha

theorem QKM.tcb_back {p : ObjRef} {y : Tcb} (hk : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ y = { x with tcbArch := y.tcbArch, tcbYieldTo := y.tcbYieldTo, tcbFault := y.tcbFault, tcbFlags := y.tcbFlags, tcbMcpriority := y.tcbMcpriority, tcbIpcBuffer := y.tcbIpcBuffer } := by
  rcases h.kh p with e | ⟨a, b, ha, hb, e⟩ | ⟨z, w, n, -, hb, -⟩
  · exact ⟨y, by rw [← e]; exact hk, rfl⟩
  · rw [hk] at hb; cases hb; exact ⟨a, ha, e⟩
  · rw [hk] at hb; cases hb

theorem QKM.sc {p : ObjRef} {z : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext z n)) :
    ∃ w, σ'.kheap p = some (.schedContext w n) ∧
      w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom } := by
  rcases h.kh p with e | ⟨a, b, ha, -, -⟩ | ⟨z', w, n', ha, hb, e⟩
  · exact ⟨z, e.trans hk, rfl⟩
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha; exact ⟨w, hb, e⟩

theorem QKM.sc_back {p : ObjRef} {w : SchedContext} {n : Nat} (hk : σ'.kheap p = some (.schedContext w n)) :
    ∃ z, σ.kheap p = some (.schedContext z n) ∧
      w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom } := by
  rcases h.kh p with e | ⟨a, b, -, hb, -⟩ | ⟨z, w', n', ha, hb, e⟩
  · exact ⟨w, by rw [← e]; exact hk, rfl⟩
  · rw [hk] at hb; cases hb
  · rw [hk] at hb; cases hb; exact ⟨z, ha, e⟩

theorem QKM.oth {p : ObjRef} {o : KernelObject} (ho : ∀ x, o ≠ .tcb x) (hs : ∀ z n, o ≠ .schedContext z n) :
    σ'.kheap p = some o ↔ σ.kheap p = some o := by
  rcases h.kh p with e | ⟨a, b, ha, hb, -⟩ | ⟨z, w, n, ha, hb, -⟩
  · rw [e]
  · rw [ha, hb]; constructor <;> intro h' <;> cases h' <;> exact absurd rfl (ho _)
  · rw [ha, hb]; constructor <;> intro h' <;> cases h' <;> exact absurd rfl (hs _ _)

theorem QKM.callKeep : Sched.CKeep σ σ' := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ⟨x, (h.oth (o := .reply x) (fun _ e => by cases e)
    (fun _ _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ?_⟩
  · obtain ⟨w, hw, e⟩ := h.sc hq; exact ⟨w, hw, by rw [e]⟩
  · obtain ⟨z, hz, -⟩ := h.sc_back hp; exact ⟨z, hz⟩

theorem QKM.ckeepP : Fl4Proofs.P3.CKeep σ σ' := by
  refine ⟨fun o => ⟨fun r cs h1 hw => ⟨cs, (h.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).1 h1, hw⟩,
    fun t ht => let ⟨x, hx, _⟩ := h.tcb_back ht; ⟨x, hx⟩, fun h0 => ?_⟩,
    fun o r cs h1 _ => (h.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h1, fun o t ht => ?_,
    h.cdt, h.orig⟩
  · rcases h.kh o with e | ⟨a, b, ha, -, -⟩ | ⟨z, w, n, ha, -, -⟩
    · rw [e, h0]
    · rw [h0] at ha; cases ha
    · rw [h0] at ha; cases ha
  · obtain ⟨y, hy, e⟩ := h.tcb ht
    exact ⟨y, hy, by rw [e]; rfl⟩

theorem QKM.kback : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨a, b, ha, hb, -⟩ | ⟨z, w, n, ha, hb, -⟩
  · exact ⟨ko', by rw [← e]; exact ho, id, id, id, id, id, id⟩
  · rw [ho] at hb; cases hb
    refine ⟨_, ha, ?_, ?_, ?_, fun _ => ⟨a, rfl⟩, ?_, ?_⟩
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, _, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
  · rw [ho] at hb; cases hb
    refine ⟨_, ha, ?_, ?_, ?_, ?_, fun _ => ⟨z, n, rfl⟩, ?_⟩
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e

theorem QKM.ksz : KSz σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨a, b, ha, hb, -⟩ | ⟨z, w, n, ha, hb, -⟩
  · exact ⟨ko', by rw [← e]; exact ho, rfl⟩
  · rw [ho] at hb; cases hb; exact ⟨_, ha, rfl⟩
  · rw [ho] at hb; cases hb; exact ⟨_, ha, rfl⟩

theorem QKM.szKeep : SzKeep σ σ' := fun p x n hp => let ⟨z, hz, _⟩ := h.sc_back hp; ⟨z, hz⟩

theorem QKM.nsc {N C : Set U64} (hN : NSC N C σ) : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p ((h.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).1 hx) hp

theorem QKM.prio (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  rcases h.kh u with e | ⟨a, b, ha, hb, e⟩ | ⟨z, w, n, ha, hb, -⟩
  · rw [e]
  · rw [ha, hb, e]; rfl
  · rw [ha, hb]

theorem QKM.isorted (hS : IpcSorted σ) : IpcSorted σ' :=
  ⟨fun p y hp => (hS.1 p y ((h.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).1 hp)).congr fun u _ => h.prio u,
    fun p y hp => (hS.2 p y ((h.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).1 hp)).congr
      fun u _ => h.prio u⟩

theorem QKM.sched {u : ObjRef} (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, z, n, hk, hsc, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
  obtain ⟨y, hy, e⟩ := h.tcb hk
  obtain ⟨w, hw, e2⟩ := h.sc hkz
  refine schedulable_of hy (by rw [e]; exact hsc) (by rw [e]; exact hrun) hw (by rw [e2]; exact hac) ?_
  rw [h.rel]; exact hnr

theorem QKM.actIdle (hA : ActIdle σ) : ActIdle σ' := by
  refine ⟨fun u hu => h.sched (hA.1 u (by rw [← h.act]; exact hu)), ?_⟩
  obtain ⟨x, h1, h2, h3, h4⟩ := hA.2
  obtain ⟨y, hy, e⟩ := h.tcb h1
  exact ⟨y, by rw [h.idle]; exact hy, by rw [e, h.isc]; exact h2, by rw [e]; exact h3, by rw [h.idle, h.rel]; exact h4⟩

theorem QKM.curInv (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
  obtain ⟨y1, n1, hk1⟩ := hC.sc
  obtain ⟨y, hy, e⟩ := h.tcb hkc
  obtain ⟨w1, hw1, -⟩ := h.sc hk1
  refine ⟨⟨y, by rw [h.ct]; exact hy, by rw [e, h.csc]; exact hcs, by rw [e]; exact hnb⟩,
    ⟨w1, n1, by rw [h.csc]; exact hw1⟩, fun hne x n hx => ?_, fun hm => hC.notRel ?_⟩
  · rw [h.csc, h.isc] at hne; rw [h.csc] at hx
    obtain ⟨z, hz, e2⟩ := h.sc_back hx
    rw [e2]; exact hC.active hne z n hz
  · rw [h.ct, h.rel] at hm; exact hm

theorem QKM.own {T C : Set U64} (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨y, hy, e⟩ := h.tcb hkt
    refine Or.inl ⟨u, hu, y, hy, by rw [e, h.csc]; exact hxs, fun x n hx => ?_,
      fun h0 hm => hnr (by rw [← h.cons]; exact h0) (by rw [h.rel] at hm; exact hm)⟩
    rw [h.csc] at hx
    obtain ⟨z, hz, e2⟩ := h.sc_back hx
    rw [e2]; exact hown z n hz
  · refine Or.inr ⟨by rw [h.csc]; exact hcs, fun x n hx => ?_⟩
    rw [h.csc] at hx
    obtain ⟨z, hz, e2⟩ := h.sc_back hx
    rw [e2]; exact hun z n hz

theorem QKM.off (hO : OffOK σ) : OffOK σ' := by
  intro h0 y n hy ha
  rw [h.cons] at h0 ⊢; rw [h.tm]
  rw [h.csc] at hy; rw [h.csc, h.isc] at ha
  obtain ⟨z, hz, e2⟩ := h.sc_back hy
  rw [e2] at ha ⊢; exact hO h0 z n hz ha

theorem QKM.curRunW (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | hR
  · refine Or.inl fun x hx => ?_
    rw [h.ct] at hx
    obtain ⟨x0, hx0, e⟩ := h.tcb_back hx
    rw [e]; exact hR x0 hx0
  · exact Or.inr (by rw [h.ct, h.idle]; exact hR)

theorem QKM.curRunM (hR : CurRunM σ) : CurRunM σ' :=
  hR.imp (fun e => by rw [h.act]; exact e) h.curRunW

theorem QKM.cur (hR : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' :=
  hR.imp (fun e => by rw [h.act]; exact e) h.curInv

theorem QKM.bsa (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · obtain ⟨x0, hx0, e⟩ := h.tcb_back hx
    obtain ⟨z, hz, e2⟩ := h.sc_back hp
    rw [e2] at hyt ⊢
    exact hB.tcb p z n t x0 hz hyt hx0 (by rw [e] at hq; exact hq)
  · obtain ⟨z, hz, e2⟩ := h.sc_back hp
    rw [e2] at hr ⊢
    exact hB.replies p z n hz hr

theorem QKM.fk : FK σ σ' := ⟨h.csc, h.idle, h.isc⟩

theorem QKM.lk {W : ObjRef → Prop} : LK W σ σ' := fun p => Or.inr (by
  rcases h.kh p with e | ⟨a, b, ha, hb, e⟩ | ⟨z, w, n, ha, hb, e⟩
  · rw [e]; exact OL.refl _
  · rw [ha, hb]
    show LObj (.tcb a) (.tcb b)
    refine ⟨fun x ex => ?_, fun x n ex => ?_, fun x ex => ?_⟩
    · cases ex; exact ⟨b, rfl, Or.inl (by rw [e])⟩
    · cases ex
    · cases ex
  · rw [ha, hb]
    show LObj (.schedContext z n) (.schedContext w n)
    refine ⟨fun x ex => ?_, fun x m ex => ?_, fun x ex => ?_⟩
    · cases ex
    · cases ex; exact ⟨w, rfl, Or.inl (by rw [e]), Or.inl (by rw [e])⟩
    · cases ex)

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The words of the TCBs, the core's node, the notifications and the SCs**
(module docstring). -/
def WideW (T N C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  (∃ y ∈ T, y.val + 256 ≤ b.val ∧ b.val < y.val + 4096) ∨
    (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288) ∨
    (∃ n ∈ N, n.val ≤ b.val ∧ b.val < n.val + 40) ∨ ScObjW C σ b

/-- `WideW`'s words are words of the other objects (`OObj`). -/
theorem WideW.oobj {T N C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S}
    {σ : Fl4Spec.State Unit} {b : U64} (h : WideW (st := st) T N C c s σ b) :
    Vs.OObj st N T C E R B c s σ b := by
  rcases h with ⟨y, hy, h1, h2⟩ | h | ⟨n, hn, h1, h2⟩ | ⟨sc, hsc, x, n, hk, ho⟩
  · exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, h2⟩))
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, by omega⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hk, ho⟩))))))

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The header words of `H`'s SCs outside `Z.C` are kept** by a
finalisation (`sc_out_keep`'s argument). -/
theorem JAtZ.wideW_scOut {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (WideW (st := st) Z.T Z.N Z.C Z.c s σ)) {q : U64} {z : Nat}
    (hq : H q = some (.sc z)) (hqC : q ∉ Z.C) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hfit := hH.fits q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal hfit
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
  rcases hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    have hne : q ≠ y := fun e => by rw [e, hHy] at hq; cases hq
    have := hH.disj q _ y _ hq hHy hne
    simp only [P1.HKind.bits] at this
    omega
  · have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
    have := J.kern.hnd q _ hq Z.c hcC
    simp only [P1.HKind.bits] at this
    omega
  · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
    have hne : q ≠ n := fun e => by rw [e, hHn] at hq; cases hq
    have := hH.disj q _ n _ hq hHn hne
    simp only [P1.HKind.bits] at this
    omega
  · have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have hne : q ≠ sc := fun e => hqC (e ▸ hsc)
    have := hH.disj q _ sc _ hq hHs hne
    simp only [P1.HKind.bits] at this
    omega

/-- **The IRQ node's caps are kept** by a finalisation (its words lie in the
kernel-state block; the TCBs, notifications and SCs outside it, the node
after it). -/
theorem JAtZ.wideW_irq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (WideW (st := st) Z.T Z.N Z.C Z.c s σ)) (i : U64) (hi : i.val < 128) :
    capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  refine irqNode_keep hw hkf J.kern.ksbAl (fun b hb => ?_) i hi
  rcases hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
  · simp only [P1.LawfulStore.nodeBase] at g1; omega
  · have := J.nk n hn; omega
  · have := (hS.scOut sc hsc x n hk b ⟨g1, g2⟩).2.2.2; omega

set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after a finalisation**: the caps kept (the slots
same), the free parts zero (no `FinW` word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state, CDT,
original bits and the node-0 `DEBUG_TCBS` word (`hDbg`). -/
theorem JAtZ.wideW_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (WideW (st := st) Z.T Z.N Z.C Z.c s σ))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (harch : σ'.archState = σ.archState)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [harch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
      omega
    · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) n.bv _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
      omega
    · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
      omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The dead stay dead across a `QKM` step** (`deadP_qk`). -/
theorem JAtZ.deadP_qm (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s3 : S} {σ3 : Fl4Spec.State Unit}
    (hA : QKM σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (WideW (st := st) Z.T Z.N Z.C Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx _ => ?_)
    (fun x hx => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx)
    (fun x hx => ⟨x, (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => ⟨x, (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx, rfl⟩)
    (fun x n hx => ?_) (fun hqC => k3 q hqC)
    (fun z hz hqC K hK8 hK => J.wideW_scOut hw hz hqC hK8 hK) hA.idle hAS hY3 (hYK.dk q.bv) hd
  · obtain ⟨y, hy, e⟩ := hA.tcb hx
    exact ⟨y, hy, by rw [e], by rw [e], Or.inl (by rw [e])⟩
  · obtain ⟨w, hw, e⟩ := hA.sc hx
    exact ⟨w, hw, Or.inl (by rw [e]), Or.inl (by rw [e])⟩

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **A TCB's `MCP` word at `J`** (module docstring): FL4's `MCP` word
(offset 3440; P1's `BlkOK` by `plainW_all`), the spec's `tcb_mcpriority`
(`XTopAt.bufSpec`, a `QKM` step), `McpRel` by `McpRel.set`; the other fields
as `JAtZ.reg_frameF` (the write a `WideW` word). -/
theorem JAtZ.mcpWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (v : U64) (m : Fl4Spec.Priority) (hv : v.val = m.toNat) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (mcpA t) v) a
      (updK σ t.bv (.tcb { x with tcbMcpriority := m })) := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hKt : (mcpA t).val = t.val + 3440 := mcpA_val hT ht
  have hwa : P1.Aligned (mcpA t) := mcpA_aligned hT ht
  set s' := L.wr s (mcpA t) v with hs'
  set σ' := updK σ t.bv (.tcb { x with tcbMcpriority := m }) with hσ'
  have hw : P1.WritesIn st s s' (· = mcpA t) := P1.writesIn_wr hwa
  obtain ⟨hblk, hfoot0, -⟩ := P1.plainW_all (K := 3440#u64) (v := v) J.blk htH (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hfoot : P1.WritesIn st s (L.wr s (mcpA t) v) (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s) := hfoot0
  have hA : QKM σ σ' := QKM.mcp hk m
  have hX' : XTopAt (L := L) AR Z s' a σ' :=
    (J.xtop.tcbWr ht 3440#u64 (Or.inl rfl) v).bufSpec (tcbMcpStep_upd hk m)
  have hks : L.ksb s' = L.ksb s := hw.1
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hwW : P1.WritesIn st s s' (WideW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    hw.mono fun b hb => Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩
  -- the words other than `t`'s `MCP` kept
  have keep : ∀ b, P1.Aligned b → b ≠ mcpA t → L.mem s' b = L.mem s b := fun b hb hne =>
    hw.mem_eq hb hne
  have hBW : BufWordRel Z.T (L.mem s') σ' := by
    refine J.buf.frame (fun u hu => keep _ (tIpcBufA_aligned (hT u hu)) fun e => ?_) (bufKeep_mcp hk m)
    have h1 := tIpcBufA_val (hT u hu)
    rw [e, hKt] at h1
    have a1 := (hT t ht).align; have a2 := (hT u hu).align
    by_cases eu : u = t
    · subst eu; omega
    · have := val_ne_of_ne eu; omega
  have hI3 := hX'.irelK (by rw [hks]; exact J.ks) hBW
  have hI := J.xtop.irelK J.ks J.buf
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb =>
    Or.inr (Or.inr (Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩))
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hwF0 : P1.WritesIn st s s (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    ⟨rfl, rfl, fun _ _ _ => rfl⟩
  -- the yield, SC-reply and reply-link words: not `t`'s `MCP` word
  have k2 : ∀ u ∈ Z.T, L.mem s' (yieldA u) = L.mem s (yieldA u) := fun u hu =>
    keep _ (yieldA_aligned hT hu) fun e => by
      have h1 := yieldA_val hT hu
      rw [e, hKt] at h1
      have a1 := (hT t ht).align; have a2 := (hT u hu).align
      by_cases eu : u = t
      · subst eu; omega
      · have := val_ne_of_ne eu; omega
  have k3 : ∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q) := fun q hq =>
    keep _ (sc_reply_word hS hq).1 fun e => by
      obtain ⟨y, n, hky, -⟩ := hs.scs q hq
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hHq := (hJ.sc q y n (J.c0 q hq) hky).2
      have hz := J.kern.heap.scmin q _ hHq
      have h128 : 2 ^ 7 ≤ 2 ^ (n + Fl4Spec.minSchedContextBits) := Nat.pow_le_pow_right (by norm_num) hz
      have hv := (sc_reply_word hS hq).2.1
      rw [e, hKt] at hv
      have hne : q ≠ t := fun e' => by rw [e', J.zH.1 t ht] at hHq; cases hHq
      have := J.kern.heap.disj q _ t _ hHq (J.zH.1 t ht) hne
      simp only [P1.HKind.bits] at this
      omega
  have k4 : ∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      keep _ (J.rp.aligned hr ha) fun e => by
        have := J.rp.tcb r hr t ht; rw [e, hKt] at ha; omega
    exact ⟨k _ (Or.inl h8), k _ (Or.inr h16)⟩
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hA.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hyk : YKeep σ σ' := by
    refine ⟨fun q y hq => ?_, fun q y n hq => ?_, fun q y n hq => ?_⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq; exact ⟨{ x with tcbMcpriority := m }, by simp [hσ', updK], rfl⟩
      · exact ⟨y, by simp [hσ', updK, e, hq], rfl⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
      · exact ⟨y, by simp [hσ', updK, e, hq], rfl⟩
    · by_cases e : q = t.bv
      · subst e; simp [hσ', updK] at hq
      · exact ⟨y, by simpa [hσ', updK, e] using hq, rfl⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qm hA hS3 hI3.1 hwW k3 hAI3.1 (J.yld.frame k2 hyk) hyk
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.wideW_irq hwW)
      (J.idleW_keep hS3 hA.idle hA.isc).2⟩
  have hkern := J.kern_keep hks hwW.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hyk, J.mcp.set hT ht hk hv, hBW, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hA.idle hA.isc), hkern,
      J.wideW_utc hwW hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, J.inv.updSame hk rfl rfl (Or.inl rfl), hA.cur J.cur,
      hA.own J.own, hA.off J.off, hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.same J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => WideW.oobj (st := st) (T := Z.T) (N := Z.N) (C := Z.C) (c := Z.c) (σ := σ)
      (Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩))
      (fun b hb u hu => Sched.tVcpuA_ne (K := 3440) hT ht hu (by rw [hb, hKt]) (by omega) (by omega)) hA.arch (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hA.szKeep hF.1 hA.kback (IpcFrKeep.of_updTcb hk rfl rfl) hC R hKd hck.orig (J.idleW_keep hS3 hA.idle hA.isc).1 J.zD⟩

end

end

end Fl4Proofs.P3
