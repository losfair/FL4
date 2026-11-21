/-
P3 (DESIGN.md §9): **`JAtZ` across a register step** (`JAtZ.reg_frame`):
FL4 writing only TCB register words (`RegW`, offsets 256..448) and the spec
changing only TCBs' saved contexts (`ArchStep`, ScYieldTo), with `IRel`
after (the register relation is `IRel`'s). No other `JAtZ` field reads a
register: the frame is `nfrStep`'s (XTopJointFinThread) with the spec's
`ArchStep` for `NFr`:

* `ArchStep.fl`, `ArchStep.callKeep`, `ArchStep.ckeepP`, `kback`, `ksz`,
  `szKeep`, `mcpKeep`, `bufKeep`, `prio`, `isorted`, `actIdle`, `curInv`,
  `own`, `off`, `curRunW`, `bsa`: what `ArchStep` keeps (every TCB but its
  `tcbArch`, every other object, every abstract field but the heap and the
  machine state);
* `JAtZ.deadP_arch`: the dead stay dead (`deadP_keep`);
* `JAtZ.reg_frame`: `XTopAt` by `XTopAt.irel_same` (the slots kept: the
  register words are TCB words, `IRel.iframe_of`), the footprint inside
  `FinW` (`finW_keeps`: the yield, MCP, buffer and call-stack words kept),
  P1's `BlkOK` and `KW` footprint given.
-/
import Fl4Proofs.P3.XTopJointFinThreadSc
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical

noncomputable section

/-- **A quiet step** (module docstring): the scheduler's abstract fields
kept; every object kept but TCBs changed in their saved context, yield-to,
fault (`cancel_ipc`'s fault clear) and flags (SetFlags; no relation of `JAtZ`
reads `tcb_flags`) and SCs changed in their consumed time
and yield-from. -/
structure QKY (σ σ' : State Unit) : Prop where
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
      y = { x with tcbArch := y.tcbArch, tcbYieldTo := y.tcbYieldTo, tcbFault := y.tcbFault, tcbFlags := y.tcbFlags }) ∨
    (∃ z w n, σ.kheap p = some (.schedContext z n) ∧ σ'.kheap p = some (.schedContext w n) ∧
      w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom })

/-- An SC's and a TCB's quiet updates. -/
theorem QKY.upd2 {σ : State Unit} {p t : ObjRef} {z w : SchedContext} {n : Nat} {x x' : Tcb}
    (hkp : σ.kheap p = some (.schedContext z n)) (hkt : σ.kheap t = some (.tcb x))
    (hw : w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom })
    (hx : x' = { x with tcbArch := x'.tcbArch, tcbYieldTo := x'.tcbYieldTo, tcbFault := x'.tcbFault, tcbFlags := x'.tcbFlags }) :
    QKY σ (updK (updSc σ p w n) t (.tcb x')) := by
  have hpt : p ≠ t := by rintro rfl; rw [hkp] at hkt; cases hkt
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
  by_cases e1 : q = t
  · subst e1; exact Or.inr (Or.inl ⟨x, x', hkt, by simp [updK], hx⟩)
  by_cases e2 : q = p
  · subst e2; exact Or.inr (Or.inr ⟨z, w, n, hkp, by simp [updK, e1], hw⟩)
  · exact Or.inl (by simp [updK, e1, e2])

section
variable {σ σ' : State Unit} (h : QKY σ σ')
include h

/-- No reply bound to a receiver gained (`ScRecvLinks`' `KhRB`). -/
theorem QKY.khrb : KhRB σ σ' := by
  intro p o' hp
  rcases h.kh p with e | ⟨x, y, h1, h2, e⟩ | ⟨z, w, n, h1, h2, -⟩
  · exact ⟨o', by rw [← e]; exact hp, ObjRB.refl o'⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.tcb (Or.inl (by rw [e]))⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)⟩

theorem QKY.tcb {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ y = { x with tcbArch := y.tcbArch, tcbYieldTo := y.tcbYieldTo, tcbFault := y.tcbFault, tcbFlags := y.tcbFlags } := by
  rcases h.kh p with e | ⟨a, b, ha, hb, e⟩ | ⟨z, w, n, ha, -, -⟩
  · exact ⟨x, e.trans hk, rfl⟩
  · rw [hk] at ha; cases ha; exact ⟨b, hb, e⟩
  · rw [hk] at ha; cases ha

theorem QKY.tcb_back {p : ObjRef} {y : Tcb} (hk : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ y = { x with tcbArch := y.tcbArch, tcbYieldTo := y.tcbYieldTo, tcbFault := y.tcbFault, tcbFlags := y.tcbFlags } := by
  rcases h.kh p with e | ⟨a, b, ha, hb, e⟩ | ⟨z, w, n, -, hb, -⟩
  · exact ⟨y, by rw [← e]; exact hk, rfl⟩
  · rw [hk] at hb; cases hb; exact ⟨a, ha, e⟩
  · rw [hk] at hb; cases hb

theorem QKY.sc {p : ObjRef} {z : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext z n)) :
    ∃ w, σ'.kheap p = some (.schedContext w n) ∧
      w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom } := by
  rcases h.kh p with e | ⟨a, b, ha, -, -⟩ | ⟨z', w, n', ha, hb, e⟩
  · exact ⟨z, e.trans hk, rfl⟩
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha; exact ⟨w, hb, e⟩

theorem QKY.sc_back {p : ObjRef} {w : SchedContext} {n : Nat} (hk : σ'.kheap p = some (.schedContext w n)) :
    ∃ z, σ.kheap p = some (.schedContext z n) ∧
      w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom } := by
  rcases h.kh p with e | ⟨a, b, -, hb, -⟩ | ⟨z, w', n', ha, hb, e⟩
  · exact ⟨w, by rw [← e]; exact hk, rfl⟩
  · rw [hk] at hb; cases hb
  · rw [hk] at hb; cases hb; exact ⟨z, ha, e⟩

theorem QKY.oth {p : ObjRef} {o : KernelObject} (ho : ∀ x, o ≠ .tcb x) (hs : ∀ z n, o ≠ .schedContext z n) :
    σ'.kheap p = some o ↔ σ.kheap p = some o := by
  rcases h.kh p with e | ⟨a, b, ha, hb, -⟩ | ⟨z, w, n, ha, hb, -⟩
  · rw [e]
  · rw [ha, hb]; constructor <;> intro h' <;> cases h' <;> exact absurd rfl (ho _)
  · rw [ha, hb]; constructor <;> intro h' <;> cases h' <;> exact absurd rfl (hs _ _)

theorem QKY.callKeep : Sched.CKeep σ σ' := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ⟨x, (h.oth (o := .reply x) (fun _ e => by cases e)
    (fun _ _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ?_⟩
  · obtain ⟨w, hw, e⟩ := h.sc hq; exact ⟨w, hw, by rw [e]⟩
  · obtain ⟨z, hz, -⟩ := h.sc_back hp; exact ⟨z, hz⟩

theorem QKY.ckeepP : Fl4Proofs.P3.CKeep σ σ' := by
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

/-- `QKY` keeps the IPC frames and the data pages. -/
theorem QKY.ipcFr : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg (C := fun _ o o' => (∃ x y, o = .tcb x ∧ o' = .tcb y ∧ y.tcbIpcframe = x.tcbIpcframe ∧
      y.tcbIpcBuffer = x.tcbIpcBuffer) ∨ ∃ z w n, o = .schedContext z n ∧ o' = .schedContext w n)
    (fun p => by
      rcases h.kh p with e | ⟨x, y, h1, h2, e⟩ | ⟨z, w, n, h1, h2, -⟩
      · exact Or.inl e
      · exact Or.inr ⟨_, _, h1, h2, Or.inl ⟨x, y, rfl, rfl, by rw [e], by rw [e]⟩⟩
      · exact Or.inr ⟨_, _, h1, h2, Or.inr ⟨z, w, n, rfl, rfl⟩⟩)
    (fun _ _ _ hc => by
      rcases hc with ⟨x, y, rfl, rfl, h1, h2⟩ | ⟨z, w, n, rfl, rfl⟩
      · exact IpcFrKeep.objFrK_tcb h1 h2
      · exact IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e))

theorem QKY.kback : KBack σ σ' := by
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

theorem QKY.ksz : KSz σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨a, b, ha, hb, -⟩ | ⟨z, w, n, ha, hb, -⟩
  · exact ⟨ko', by rw [← e]; exact ho, rfl⟩
  · rw [ho] at hb; cases hb; exact ⟨_, ha, rfl⟩
  · rw [ho] at hb; cases hb; exact ⟨_, ha, rfl⟩

theorem QKY.szKeep : SzKeep σ σ' := fun p x n hp => let ⟨z, hz, _⟩ := h.sc_back hp; ⟨z, hz⟩

theorem QKY.mcpKeep : McpKeep σ σ' := fun p x hp => by
  obtain ⟨y, hy, e⟩ := h.tcb hp; exact ⟨y, hy, by rw [e]⟩

theorem QKY.bufKeep : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧
    y.tcbIpcBuffer = x.tcbIpcBuffer := fun p x hp => by
  obtain ⟨y, hy, e⟩ := h.tcb hp; exact ⟨y, hy, by rw [e]⟩

theorem QKY.nsc {N C : Set U64} (hN : NSC N C σ) : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p ((h.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).1 hx) hp

theorem QKY.prio (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  rcases h.kh u with e | ⟨a, b, ha, hb, e⟩ | ⟨z, w, n, ha, hb, -⟩
  · rw [e]
  · rw [ha, hb, e]; rfl
  · rw [ha, hb]

theorem QKY.isorted (hS : IpcSorted σ) : IpcSorted σ' :=
  ⟨fun p y hp => (hS.1 p y ((h.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).1 hp)).congr fun u _ => h.prio u,
    fun p y hp => (hS.2 p y ((h.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).1 hp)).congr
      fun u _ => h.prio u⟩

theorem QKY.sched {u : ObjRef} (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, z, n, hk, hsc, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
  obtain ⟨y, hy, e⟩ := h.tcb hk
  obtain ⟨w, hw, e2⟩ := h.sc hkz
  refine schedulable_of hy (by rw [e]; exact hsc) (by rw [e]; exact hrun) hw (by rw [e2]; exact hac) ?_
  rw [h.rel]; exact hnr

theorem QKY.actIdle (hA : ActIdle σ) : ActIdle σ' := by
  refine ⟨fun u hu => h.sched (hA.1 u (by rw [← h.act]; exact hu)), ?_⟩
  obtain ⟨x, h1, h2, h3, h4⟩ := hA.2
  obtain ⟨y, hy, e⟩ := h.tcb h1
  exact ⟨y, by rw [h.idle]; exact hy, by rw [e, h.isc]; exact h2, by rw [e]; exact h3, by rw [h.idle, h.rel]; exact h4⟩

theorem QKY.curInv (hC : CurInv σ) : CurInv σ' := by
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

theorem QKY.own {T C : Set U64} (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
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

theorem QKY.off (hO : OffOK σ) : OffOK σ' := by
  intro h0 y n hy ha
  rw [h.cons] at h0 ⊢; rw [h.tm]
  rw [h.csc] at hy; rw [h.csc, h.isc] at ha
  obtain ⟨z, hz, e2⟩ := h.sc_back hy
  rw [e2] at ha ⊢; exact hO h0 z n hz ha

theorem QKY.curRunW (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | hR
  · refine Or.inl fun x hx => ?_
    rw [h.ct] at hx
    obtain ⟨x0, hx0, e⟩ := h.tcb_back hx
    rw [e]; exact hR x0 hx0
  · exact Or.inr (by rw [h.ct, h.idle]; exact hR)

theorem QKY.curRunM (hR : CurRunM σ) : CurRunM σ' :=
  hR.imp (fun e => by rw [h.act]; exact e) h.curRunW

theorem QKY.cur (hR : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' :=
  hR.imp (fun e => by rw [h.act]; exact e) h.curInv

theorem QKY.bsa (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · obtain ⟨x0, hx0, e⟩ := h.tcb_back hx
    obtain ⟨z, hz, e2⟩ := h.sc_back hp
    rw [e2] at hyt ⊢
    exact hB.tcb p z n t x0 hz hyt hx0 (by rw [e] at hq; exact hq)
  · obtain ⟨z, hz, e2⟩ := h.sc_back hp
    rw [e2] at hr ⊢
    exact hB.replies p z n hz hr

theorem QKY.fk : FK σ σ' := ⟨h.csc, h.idle, h.isc⟩

theorem QKY.lk {W : ObjRef → Prop} : LK W σ σ' := fun p => Or.inr (by
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
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The dead stay dead across a quiet step** (`deadP_keep`). -/
theorem JAtZ.deadP_qk (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s3 : S} {σ3 : Fl4Spec.State Unit}
    (hA : QKY σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx _ => ?_)
    (fun x hx => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx)
    (fun x hx => ⟨x, (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => ⟨x, (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx, rfl⟩)
    (fun x n hx => ?_) (fun hqC => k3 q hqC)
    (fun z hz hqC K hK8 hK => J.finW_scOut hw hz hqC hK8 hK) hA.idle hAS hY3 (hYK.dk q.bv) hd
  · obtain ⟨y, hy, e⟩ := hA.tcb hx
    exact ⟨y, hy, by rw [e], by rw [e], Or.inl (by rw [e])⟩
  · obtain ⟨w, hw, e⟩ := hA.sc hx
    exact ⟨w, hw, Or.inl (by rw [e]), Or.inl (by rw [e])⟩

/-- The words a register step writes: TCB registers and SCs' `CONSUMED`
words. -/
def RegCW (T C : Set U64) (b : U64) : Prop :=
  (∃ y ∈ T, y.val + 256 ≤ b.val ∧ b.val < y.val + 448) ∨ ∃ q ∈ C, b = scW q 8#u64

/-- `RegCW` with the TCBs' fault words (offset 3376, `cancel_ipc`'s
`clear_fault`). -/
def RegFW (T C : Set U64) (b : U64) : Prop := RegCW T C b ∨ ∃ y ∈ T, b.val = y.val + 3376

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a register step** (module docstring): FL4 writing TCB
registers and fault words and SCs' consumed words, the spec a quiet step
keeping the yield fields (`YKeep`), `Inv` after given (`Inv.scFields`,
`ArchStep.inv`). -/
theorem JAtZ.reg_frameF (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (RegFW Z.T Z.C)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst D s' a σ' := by
  have hI := J.xtop.irelK J.ks J.buf
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb => by
    rcases hb with (hb | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩
    · obtain ⟨y, hy, h1, h2⟩ := hb
      exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, by omega⟩))
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 8#u64) (by simp) (by simp)).2⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
  have hwF : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw.mono fun b hb => by
    rcases hb with (⟨y, hy, k1, k2⟩ | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inl (KFoot.of_sw (sw_hdr hS hq (K := 8#u64) (by simp) (by simp) (by decide)))
    · exact Or.inr ⟨y, hy, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hwF
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hA.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qk hA hS3 hI3.1 hwF k3 hAI3.1 (J.yld.frame k2 hyk) hyk
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.finW_irq hwF)
      (J.idleW_keep hS3 hA.idle hA.isc).2⟩
  have hkern := J.kern_keep hks hwF.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac' Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hyk, J.mcp.frame k1 hA.mcpKeep, J.buf.frame kb hA.bufKeep, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hA.idle hA.isc), hkern,
      J.finW_utc hwF hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, hInv, hA.cur J.cur, hA.own J.own, hA.off J.off,
      hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.same J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hwF (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) hA.arch (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hA.szKeep hF.1 hA.kback hA.ipcFr hC R hKd hck.orig (J.idleW_keep hS3 hA.idle hA.isc).1 J.zD⟩

/-- **`JAtZ` across a register step** (`reg_frameF` without fault words). -/
theorem JAtZ.reg_frame (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (RegCW Z.T Z.C)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst D s' a σ' :=
  J.reg_frameF hI3 (hw.mono fun _ h => Or.inl h) hA hyk hInv hblk hfoot

end

end

end Fl4Proofs.P3
