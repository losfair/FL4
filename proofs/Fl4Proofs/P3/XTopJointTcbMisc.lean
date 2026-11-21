/-
P3 (DESIGN.md §9), TCB: **steps of the Thread cap's remaining labels at
`J`** (for XTopJointTcb's WriteFPU, SetTimer, …).

* `JAtZ.reg_frameFp`: XTopJointRegFrame's register frame (`JAtZ.reg_frameF`)
  widened to the TCBs' FPU images (offsets 512..3208: TCB words read by no
  relation of `JAtZ`; the spec's FPU state is not related to FL4's, see
  XTopJointFpu).
* `JAtZ.fpuWrJ`: one word of a TCB's FPU image written at `J`, the spec state
  kept (`XTopAt.tcbWrF`, P1's `BlkOK` by `blk_rf`, its footprint by
  `foot_field`).
* `JAtZ.copyFpuJ`: FL4's `copy_words` into a TCB's FPU image (WriteFPU's
  copy) at `J` (`copy_words_inv` with `JAtZ.fpuWrJ`).
* `JAtZ.archJ`: `JAtZ` at another arch state related to the same CR3 (the
  FPU operations of the arch backend: `ARKeep` [P]).
* `Sched.BKY` (with `bky_bind` and QKY's lemmas): the spec frame of
  `bind_notification`, TCBs changed in their bound notification and
  notifications in their bound TCB only.
* `JAtZ.cover_tn`: a thread cap and a notification cap in slots cover their
  objects (`JAtZ.cover_cap` with no write).
* `JAtZ.bindNJ`: `bind_notification` at `J` (`bound_wr_irel`, the footprint
  `FinW`, `Inv.updNtfn`/`Inv.tcbUpd`, P1's `bind_notification.blk` and
  `Foot`); the thread and the notification leave the dead set (`D \ {t, n}`),
  covered by their caps; no premise.
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec's frame of `bind_notification` -/

namespace Sched
open Fl4Spec

/-- **A bind step** (`bind_notification`'s spec frame, as `QKY`): the
scheduler's abstract fields kept; every object kept but TCBs changed in
their bound notification and notifications in their bound TCB. -/
structure BKY (σ σ' : State Unit) : Prop where
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
      y = { x with tcbBoundNotification := y.tcbBoundNotification }) ∨
    (∃ x y, σ.kheap p = some (.notification x) ∧ σ'.kheap p = some (.notification y) ∧
      y = { x with ntfnBoundTcb := y.ntfnBoundTcb })

/-- The spec's `bind_notification` outcome is a `BKY` step. -/
theorem bky_bind {σ : State Unit} {t n : ObjRef} {x x' : Tcb} {xn xn' : Notification}
    (hk : σ.kheap t = some (.tcb x)) (hkn : σ.kheap n = some (.notification xn))
    (ex : x' = { x with tcbBoundNotification := x'.tcbBoundNotification })
    (en : xn' = { xn with ntfnBoundTcb := xn'.ntfnBoundTcb }) :
    BKY σ (Notif.updK (Notif.updK σ n (.notification xn')) t (.tcb x')) := by
  have htn : t ≠ n := by rintro rfl; rw [hk] at hkn; cases hkn
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => ?_⟩
  by_cases e1 : p = t
  · subst e1; exact Or.inr (Or.inl ⟨x, x', hk, by simp [Notif.updK], ex⟩)
  · by_cases e2 : p = n
    · subst e2; exact Or.inr (Or.inr ⟨xn, xn', hkn, by simp [Notif.updK, e1], en⟩)
    · exact Or.inl (by simp [Notif.updK, e1, e2])

section
variable {σ σ' : State Unit} (h : BKY σ σ')
include h

/-- No reply bound to a receiver gained (`ScRecvLinks`' `KhRB`). -/
theorem BKY.khrb : KhRB σ σ' := by
  intro p o' hp
  rcases h.kh p with e | ⟨x, y, h1, h2, e⟩ | ⟨z, w, h1, h2, -⟩
  · exact ⟨o', by rw [← e]; exact hp, ObjRB.refl o'⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.tcb (Or.inl (by rw [e]))⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)⟩

theorem BKY.tcb {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ y = { x with tcbBoundNotification := y.tcbBoundNotification } := by
  rcases h.kh p with e | ⟨a, b, ha, hb, e⟩ | ⟨a, b, ha, -, -⟩
  · exact ⟨x, e.trans hk, rfl⟩
  · rw [hk] at ha; cases ha; exact ⟨b, hb, e⟩
  · rw [hk] at ha; cases ha

theorem BKY.tcb_back {p : ObjRef} {y : Tcb} (hk : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ y = { x with tcbBoundNotification := y.tcbBoundNotification } := by
  rcases h.kh p with e | ⟨a, b, ha, hb, e⟩ | ⟨a, b, -, hb, -⟩
  · exact ⟨y, by rw [← e]; exact hk, rfl⟩
  · rw [hk] at hb; cases hb; exact ⟨a, ha, e⟩
  · rw [hk] at hb; cases hb

theorem BKY.ntfn_back {p : ObjRef} {y : Notification} (hk : σ'.kheap p = some (.notification y)) :
    ∃ x, σ.kheap p = some (.notification x) ∧ y = { x with ntfnBoundTcb := y.ntfnBoundTcb } := by
  rcases h.kh p with e | ⟨a, b, -, hb, -⟩ | ⟨a, b, ha, hb, e⟩
  · exact ⟨y, by rw [← e]; exact hk, rfl⟩
  · rw [hk] at hb; cases hb
  · rw [hk] at hb; cases hb; exact ⟨a, ha, e⟩

theorem BKY.oth {p : ObjRef} {o : KernelObject} (ho : ∀ x, o ≠ .tcb x) (hs : ∀ x, o ≠ .notification x) :
    σ'.kheap p = some o ↔ σ.kheap p = some o := by
  rcases h.kh p with e | ⟨a, b, ha, hb, -⟩ | ⟨a, b, ha, hb, -⟩
  · rw [e]
  · rw [ha, hb]; constructor <;> intro h' <;> cases h' <;> exact absurd rfl (ho _)
  · rw [ha, hb]; constructor <;> intro h' <;> cases h' <;> exact absurd rfl (hs _)

theorem BKY.sc {p : ObjRef} {z : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext z n)) :
    ∃ w, σ'.kheap p = some (.schedContext w n) ∧
      w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom } :=
  ⟨z, (h.oth (fun _ e => by cases e) (fun _ e => by cases e)).2 hk, rfl⟩

theorem BKY.sc_back {p : ObjRef} {w : SchedContext} {n : Nat} (hk : σ'.kheap p = some (.schedContext w n)) :
    ∃ z, σ.kheap p = some (.schedContext z n) ∧
      w = { z with scConsumed := w.scConsumed, scYieldFrom := w.scYieldFrom } :=
  ⟨w, (h.oth (fun _ e => by cases e) (fun _ e => by cases e)).1 hk, rfl⟩

theorem BKY.callKeep : Sched.CKeep σ σ' := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ⟨x, (h.oth (o := .reply x) (fun _ e => by cases e)
    (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ?_⟩
  · obtain ⟨w, hw, e⟩ := h.sc hq; exact ⟨w, hw, by rw [e]⟩
  · obtain ⟨z, hz, -⟩ := h.sc_back hp; exact ⟨z, hz⟩

theorem BKY.ckeepP : Fl4Proofs.P3.CKeep σ σ' := by
  refine ⟨fun o => ⟨fun r cs h1 hw => ⟨cs, (h.oth (fun _ e => by cases e) (fun _ e => by cases e)).1 h1, hw⟩,
    fun t ht => let ⟨x, hx, _⟩ := h.tcb_back ht; ⟨x, hx⟩, fun h0 => ?_⟩,
    fun o r cs h1 _ => (h.oth (fun _ e => by cases e) (fun _ e => by cases e)).2 h1, fun o t ht => ?_,
    h.cdt, h.orig⟩
  · rcases h.kh o with e | ⟨a, b, ha, -, -⟩ | ⟨a, b, ha, -, -⟩
    · rw [e, h0]
    · rw [h0] at ha; cases ha
    · rw [h0] at ha; cases ha
  · obtain ⟨y, hy, e⟩ := h.tcb ht
    exact ⟨y, hy, by rw [e]; rfl⟩

/-- `BKY` keeps the IPC frames and the data pages. -/
theorem BKY.ipcFr : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg (C := fun _ o o' => (∃ x y, o = .tcb x ∧ o' = .tcb y ∧ y.tcbIpcframe = x.tcbIpcframe ∧
      y.tcbIpcBuffer = x.tcbIpcBuffer) ∨ ∃ z w, o = .notification z ∧ o' = .notification w)
    (fun p => by
      rcases h.kh p with e | ⟨x, y, h1, h2, e⟩ | ⟨z, w, h1, h2, -⟩
      · exact Or.inl e
      · exact Or.inr ⟨_, _, h1, h2, Or.inl ⟨x, y, rfl, rfl, by rw [e], by rw [e]⟩⟩
      · exact Or.inr ⟨_, _, h1, h2, Or.inr ⟨z, w, rfl, rfl⟩⟩)
    (fun _ _ _ hc => by
      rcases hc with ⟨x, y, rfl, rfl, h1, h2⟩ | ⟨z, w, rfl, rfl⟩
      · exact IpcFrKeep.objFrK_tcb h1 h2
      · exact IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e))

theorem BKY.kback : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨a, b, ha, hb, -⟩ | ⟨a, b, ha, hb, -⟩
  · exact ⟨ko', by rw [← e]; exact ho, id, id, id, id, id, id⟩
  · rw [ho] at hb; cases hb
    refine ⟨_, ha, ?_, ?_, ?_, fun _ => ⟨a, rfl⟩, ?_, ?_⟩
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, _, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
  · rw [ho] at hb; cases hb
    refine ⟨_, ha, fun _ => ⟨a, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, e⟩; cases e
    · rintro ⟨_, _, e⟩; cases e
    · rintro ⟨_, e⟩; cases e

theorem BKY.ksz : KSz σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨a, b, ha, hb, -⟩ | ⟨a, b, ha, hb, -⟩
  · exact ⟨ko', by rw [← e]; exact ho, rfl⟩
  · rw [ho] at hb; cases hb; exact ⟨_, ha, rfl⟩
  · rw [ho] at hb; cases hb; exact ⟨_, ha, rfl⟩

theorem BKY.szKeep : SzKeep σ σ' := fun p x n hp => let ⟨z, hz, _⟩ := h.sc_back hp; ⟨z, hz⟩

theorem BKY.mcpKeep : McpKeep σ σ' := fun p x hp => by
  obtain ⟨y, hy, e⟩ := h.tcb hp; exact ⟨y, hy, by rw [e]⟩

theorem BKY.bufKeep : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧
    y.tcbIpcBuffer = x.tcbIpcBuffer := fun p x hp => by
  obtain ⟨y, hy, e⟩ := h.tcb hp; exact ⟨y, hy, by rw [e]⟩

theorem BKY.ykeep : YKeep σ σ' :=
  ⟨fun p x hp => by obtain ⟨y, hy, e⟩ := h.tcb hp; exact ⟨y, hy, by rw [e]⟩,
    fun p x n hp => ⟨x, (h.oth (fun _ e => by cases e) (fun _ e => by cases e)).2 hp, rfl⟩,
    fun p y n hp => ⟨y, (h.oth (fun _ e => by cases e) (fun _ e => by cases e)).1 hp, rfl⟩⟩

theorem BKY.nsc {N C : Set U64} (hN : NSC N C σ) : NSC N C σ' := fun n hn x p hx hp => by
  obtain ⟨x0, hx0, e⟩ := h.ntfn_back hx
  exact hN n hn x0 p hx0 (by rw [e] at hp; exact hp)

theorem BKY.prio (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  rcases h.kh u with e | ⟨a, b, ha, hb, e⟩ | ⟨a, b, ha, hb, -⟩
  · rw [e]
  · rw [ha, hb, e]; rfl
  · rw [ha, hb]

theorem BKY.isorted (hS : IpcSorted σ) : IpcSorted σ' := by
  refine ⟨fun p y hp => (hS.1 p y ((h.oth (fun _ e => by cases e) (fun _ e => by cases e)).1 hp)).congr
    fun u _ => h.prio u, fun p y hp => ?_⟩
  obtain ⟨x0, hx0, e⟩ := h.ntfn_back hp
  rw [e]
  exact (hS.2 p x0 hx0).congr fun u _ => h.prio u

theorem BKY.sched {u : ObjRef} (hs : schedulable u σ = true) : schedulable u σ' = true := by
  obtain ⟨x, scp, z, n, hk, hsc, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
  obtain ⟨y, hy, e⟩ := h.tcb hk
  obtain ⟨w, hw, e2⟩ := h.sc hkz
  refine schedulable_of hy (by rw [e]; exact hsc) (by rw [e]; exact hrun) hw (by rw [e2]; exact hac) ?_
  rw [h.rel]; exact hnr

theorem BKY.actIdle (hA : ActIdle σ) : ActIdle σ' := by
  refine ⟨fun u hu => h.sched (hA.1 u (by rw [← h.act]; exact hu)), ?_⟩
  obtain ⟨x, h1, h2, h3, h4⟩ := hA.2
  obtain ⟨y, hy, e⟩ := h.tcb h1
  exact ⟨y, by rw [h.idle]; exact hy, by rw [e, h.isc]; exact h2, by rw [e]; exact h3, by rw [h.idle, h.rel]; exact h4⟩

theorem BKY.curInv (hC : CurInv σ) : CurInv σ' := by
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

theorem BKY.own {T C : Set U64} (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
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

theorem BKY.off (hO : OffOK σ) : OffOK σ' := by
  intro h0 y n hy ha
  rw [h.cons] at h0 ⊢; rw [h.tm]
  rw [h.csc] at hy; rw [h.csc, h.isc] at ha
  obtain ⟨z, hz, e2⟩ := h.sc_back hy
  rw [e2] at ha ⊢; exact hO h0 z n hz ha

theorem BKY.curRunW (hR : CurRunW σ) : CurRunW σ' := by
  rcases hR with hR | hR
  · refine Or.inl fun x hx => ?_
    rw [h.ct] at hx
    obtain ⟨x0, hx0, e⟩ := h.tcb_back hx
    rw [e]; exact hR x0 hx0
  · exact Or.inr (by rw [h.ct, h.idle]; exact hR)

theorem BKY.curRunM (hR : CurRunM σ) : CurRunM σ' :=
  hR.imp (fun e => by rw [h.act]; exact e) h.curRunW

theorem BKY.cur (hR : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' :=
  hR.imp (fun e => by rw [h.act]; exact e) h.curInv

theorem BKY.bsa (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · obtain ⟨x0, hx0, e⟩ := h.tcb_back hx
    obtain ⟨z, hz, e2⟩ := h.sc_back hp
    rw [e2] at hyt ⊢
    exact hB.tcb p z n t x0 hz hyt hx0 (by rw [e] at hq; exact hq)
  · obtain ⟨z, hz, e2⟩ := h.sc_back hp
    rw [e2] at hr ⊢
    exact hB.replies p z n hz hr

end

end Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a register step with FPU-image words** (as
XTopJointTcb's `JAtZ.reg_frameG`, the write set widened by the TCBs' FPU
images, offsets 512..3208). -/
theorem JAtZ.reg_frameFp (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (fun b => RegFW Z.T Z.C b ∨ ∃ y ∈ Z.T,
      y.val + 512 ≤ b.val ∧ b.val < y.val + 3208)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst D s' a σ' := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb => by
    rcases hb with ((hb | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩) | ⟨y, hy, h1, h2⟩
    · obtain ⟨y, hy, h1, h2⟩ := hb
      exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, by omega⟩))
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 8#u64) (by simp) (by simp)).2⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
  have hwF : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw.mono fun b hb => by
    rcases hb with ((⟨y, hy, k1, k2⟩ | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩) | ⟨y, hy, k1, k2⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inl (KFoot.of_sw (sw_hdr hS hq (K := 8#u64) (by simp) (by simp) (by decide)))
    · exact Or.inr ⟨y, hy, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
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

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **A word of a TCB's FPU image written at `J`** (`JAtZ.reg_frameFp` with
the spec state kept: `XTopAt.tcbWrF`, `IRel` by `XTopAt.irelK`, P1's `BlkOK`
by `blk_rf`, its footprint by `foot_field`). -/
theorem JAtZ.fpuWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (wa : U64)
    (Kv : Nat) (hK : 512 ≤ Kv ∧ Kv < 3208 ∧ Kv % 8 = 0) (hwav : wa.val = t.val + Kv) (v : U64) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s wa v) a σ := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hT
  set K : U64 := ⟨BitVec.ofNat 64 Kv⟩ with hKdef
  have hKv : K.val = Kv := by
    show (BitVec.ofNat 64 Kv).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hKt : (core.num.U64.wrapping_add t K).val = t.val + K.val := tfield_val hta (by omega)
  have hreq : wa = core.num.U64.wrapping_add t K := UScalar.eq_of_val_eq (by rw [hwav, hKt, hKv])
  subst hreq
  have hwa : P1.Aligned (core.num.U64.wrapping_add t K) := P1.field_aligned hta (by omega) (by omega)
  have hw : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (· = core.num.U64.wrapping_add t K) :=
    P1.writesIn_wr hwa
  have hblk := (P1.blk_rf J.blk (hw.mono fun b hb => Or.inl ⟨t, htH, K, by omega, by omega, hb⟩)).1
  have hfoot : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (P1.KW st (P1.Heap.tcbs H) Cs
      (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) :=
    P1.foot_field hTH htH (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
  have hX' := J.xtop.tcbWrF ht _ Kv hK (by rw [hKt, hKv]) v
  have hks : L.ksb (L.wr s (core.num.U64.wrapping_add t K) v) = L.ksb s := hw.1
  have hwF : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    hw.mono fun b hb => Or.inr ⟨t, ht, Kv, by omega, by omega, by omega, by omega, by omega, by rw [hb, hKt, hKv]⟩
  obtain ⟨-, -, kb, -, -⟩ := J.finW_keeps hwF
  have hA : QKY σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => Or.inl rfl⟩
  have hBW : BufWordRel Z.T (L.mem (L.wr s (core.num.U64.wrapping_add t K) v)) σ := J.buf.frame kb hA.bufKeep
  have hI3 := hX'.irelK (by rw [hks]; exact J.ks) hBW
  exact J.reg_frameFp hI3 (hw.mono fun b hb => Or.inr ⟨t, ht, by rw [hb, hKt, hKv]; omega,
    by rw [hb, hKt, hKv]; omega⟩) hA (YKeep.of_kheap rfl) J.inv hblk hfoot

set_option maxHeartbeats 8000000 in
/-- **WriteFPU's copy into a TCB's FPU image at `J`** (`copy_words_inv`,
each word by `JAtZ.fpuWrJ`). -/
theorem JAtZ.copyFpuJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (src : U64) :
    tcb.copy_words st s src (core.num.U64.wrapping_add t layout.tcb.FPU) 337#u64 ⦃ s' =>
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ ⦄ := by
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hpf := (hcq.tcbs t ht).fits
  have hpa := (hcq.tcbs t ht).align
  have hfpu : (core.num.U64.wrapping_add t layout.tcb.FPU).val = t.val + 512 := by
    unfold layout.tcb.FPU
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine copy_words_inv (fun s' => ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ) s src _ _
    ⟨Z.vs, J⟩ ?_
  rintro s2 i ⟨V, J2⟩ hi v
  have hiv : (core.num.U64.wrapping_mul i 8#u64).val = 8 * i.val := by
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    have : i.val < 337 := hi
    omega
  have hi' : i.val < 337 := hi
  obtain ⟨V', J3⟩ := J2.fpuWrJ (t := t) ht
    (core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.FPU) (core.num.U64.wrapping_mul i 8#u64))
    (512 + 8 * i.val) ⟨by omega, by omega, by omega⟩ (by
    have h1 : (core.num.U64.wrapping_add t layout.tcb.FPU).val + (core.num.U64.wrapping_mul i 8#u64).val < 2 ^ 64 := by
      rw [hfpu, hiv]; omega
    clear h1
    unfold layout.tcb.FPU
    simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
    simp [U64.size, U64.numBits]
    omega) v
  exact ⟨V', J3⟩

/-- **`JAtZ` at another arch state related to the same CR3** (`JAtZ.arFrS`
with the spec state kept, `XTopAt.arch`). -/
theorem JAtZ.archJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {a' : A}
    (hAR : AR a' σ.archState.x64CurrentCr3) : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a' σ :=
  J.arFrS (arFr_fpuOwner σ σ.machineState σ.archState.x64CurrentFpuOwner) (J.xtop.arch hAR)

/-- **A thread cap and a notification cap in slots cover their objects**
(`JAtZ.cover_cap` with no write). -/
theorem JAtZ.cover_tn (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t n : U64} (ht : t ∈ Z.T) (hn : n ∈ Z.N)
    {xT xN : U64} (hxT : IsSlot Z.th xT) (hcT : capAt (L.mem s) xT = ok (.Thread t))
    (hxN : IsSlot Z.th xN) {nb : U64} {nw nr : Bool} (hcN : capAt (L.mem s) xN = ok (.Notification n nb nw nr)) :
    ((∀ k, Z.th t = some k → Sched.Covered (L.mem s) Z.G t.val (t.val + max (objSize k) 1)) ∧
      (∀ k, H t = some k → Sched.Covered (L.mem s) Z.G t.val (t.val + 2 ^ k.bits))) ∧
    ((∀ k, Z.th n = some k → Sched.Covered (L.mem s) Z.G n.val (n.val + max (objSize k) 1)) ∧
      (∀ k, H n = some k → Sched.Covered (L.mem s) Z.G n.val (n.val + 2 ^ k.bits))) := by
  have hH := J.kern.heap
  have hHt : H t = some .tcb := J.zH.1 t ht
  have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
  have hft := hH.fits t _ hHt
  have hfn := hH.fits n _ hHn
  simp only [P1.HKind.bits] at hft hfn
  refine ⟨J.cover_cap (P1.WritesIn.refl s _) hxT hcT (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_thread t hft) fun k hk => ?_, J.cover_cap (P1.WritesIn.refl s _) hxN hcN (fun h => by cases h)
    (ok_inj (phys_eq _).symm) rfl (range_ntfn n nb nw nr hfn) fun k hk => ?_⟩
  · rw [hHt] at hk; cases hk
    exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  · rw [hHn] at hk; cases hk
    exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩

open Fl4Proofs.P1 in
set_option maxHeartbeats 16000000 in
/-- **`bind_notification` at `J`** (module docstring): FL4's two writes
(`bind_ntfn_eq`) against the spec's (`bindNotification_eq`), `IRel` after
(`bound_wr_irel`), the footprint `FinW` (as `unbindNJ`'s), the spec frame
`BKY` with `Inv` after (`Inv.updNtfn`, `Inv.tcbUpd`), P1's
`bind_notification.blk` and its footprint (as `unbind_notification.blkF`);
the thread and the notification leave the dead set, covered by their caps
(`JAtZ.cover_tn`). -/
theorem JAtZ.bindNJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t n : U64} (ht : t ∈ Z.T) (hn : n ∈ Z.N)
    (hn0 : n ≠ 0#u64) {xT xN : U64} (hxT : IsSlot Z.th xT) (hcT : capAt (L.mem s) xT = ok (.Thread t))
    (hxN : IsSlot Z.th xN) {nb : U64} {nw nr : Bool} (hcN : capAt (L.mem s) xN = ok (.Notification n nb nw nr)) :
    notification.bind_notification st s t n ⦃ s' => ∃ σ',
      Fl4Spec.bindNotification (Z := Unit) t.bv n.bv σ = ({((), σ')}, False) ∧
      ∃ V D', JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D' s' a σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  obtain ⟨x, hk, -⟩ := hI.1.tcb t ht
  obtain ⟨xn, hkn, -⟩ := hI.1.ntfn n hn
  have ht0 : t ≠ 0#u64 := fun e => (hP0.e.tcb t ht).ne0 (by rw [e]; rfl)
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hnH : n ∈ P1.Heap.ntfns H := J.zH.2.2.2 n hn
  obtain ⟨⟨cT1, cT2⟩, ⟨cN1, cN2⟩⟩ := J.cover_tn ht hn hxT hcT hxN hcN
  -- P1's `BlkOK` and footprint
  have hblk0 := P1.notification.bind_notification.blk s t n J.blk htH hnH
  rw [Sched.bind_ntfn_eq s t n, WP.spec_ok] at hblk0
  have hb := J.blk
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hm : P1.ntfnBtA n ∈ P1.Heap.frame H := (hb.2.2.1.1.ntB n hnH).2
  have f1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s
      (L.wr s (P1.ntfnBtA n) t) :=
    P1.foot_wr (hb.1.choose_spec.choose_spec.omega _ (hb.2.2.2.2.sub _ hm)).1 (P1.kw_sg hm)
  have hfoot0 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s
      (L.wr (L.wr s (P1.ntfnBtA n) t) (core.num.U64.wrapping_add t 3368#u64) n) :=
    f1.trans (P1.foot_field (K := 3368#u64) hT htH (by simp) (by simp) (by simp) (by simp))
  have hfoot : P1.WritesIn st s (L.wr (L.wr s (Notif.nBoundA n) t) (P1.boundA t) n) (P1.KW st (P1.Heap.tcbs H) Cs
      (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) := hfoot0
  rw [Sched.bind_ntfn_eq s t n, WP.spec_ok]
  -- `IRel` after
  have hX2 := bound_wr_irel hP0 hI ht hn hk hkn t n (fun _ => ht)
  rw [Notif.optRef_ne ht0, Notif.optRef_ne hn0] at hX2
  have he := Sched.bindNotification_eq hkn hk
  refine ⟨_, he, ?_⟩
  have F : Sched.BKY σ (Notif.updK (Notif.updK σ n.bv (.notification { xn with ntfnBoundTcb := some t.bv })) t.bv
      (.tcb { x with tcbBoundNotification := some n.bv })) := Sched.bky_bind hk hkn rfl rfl
  set σ' : Fl4Spec.State Unit := Notif.updK (Notif.updK σ n.bv (.notification { xn with ntfnBoundTcb := some t.bv }))
    t.bv (.tcb { x with tcbBoundNotification := some n.bv }) with hσ'
  -- the footprint
  have hba : Aligned (nBoundA n) := by rw [nBoundA_eq]; exact (nword hP0.n hn (K := 24#u64) (by simp) (by simp)).1
  have hbv : (nBoundA n).val = n.val + 24 := by rw [nBoundA_eq]; exact nfield_val (hP0.n.ntfn n hn) (by simp)
  have hpa := hP0.e.tcb _ ht
  have hta := (a_bound hpa).1
  have hbvp := val_bound hpa
  have hw2 := (writesIn_wr (s := s) (v := t) hba).trans
    (writesIn_wr (s := L.wr s (nBoundA n) t) (v := n) hta)
  have hF : IFrame (L := L) Z.th s (L.wr (L.wr s (nBoundA n) t) (P1.boundA t) n) :=
    IRel.iframe_of hI hw2 fun b hb => by
      rcases hb with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, by rw [hbv]; omega, by rw [hbv]; omega⟩)))))
      · exact Or.inr (Or.inr (Or.inl ⟨_, ht, by rw [hbvp]; omega, by rw [hbvp]; omega⟩))
  have hw : P1.WritesIn st s (L.wr (L.wr s (nBoundA n) t) (P1.boundA t) n)
      (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw2.mono fun b hb => by
    rcases hb with rfl | rfl
    · exact NWrite.finW hP0.e.tcb (Or.inl ⟨n, hn, by rw [hbv]; omega, by rw [hbv]; omega⟩)
    · exact finW_bound hP0.e.tcb ht
  -- the spec's `Inv`
  have htn : t.bv ≠ n.bv := by intro e; rw [e] at hk; rw [hk] at hkn; cases hkn
  have I1 := J.inv.updNtfn hkn (x' := { xn with ntfnBoundTcb := some t.bv })
    (fun p hp => J.inv.ntfnSc n.bv xn p hkn hp)
  have hkt1 : (Notif.updK σ n.bv (.notification { xn with ntfnBoundTcb := some t.bv })).kheap t.bv =
      some (.tcb x) := by simp [Notif.updK, htn, hk]
  have I3 := I1.tcbUpd hkt1 { x with tcbBoundNotification := some n.bv } rfl rfl rfl
  -- the assembly (as `JAtZ.reg_frameFp`)
  have hck : Fl4Proofs.P3.CKeep σ σ' := F.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hX2 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb (L.wr (L.wr s (nBoundA n) t) (P1.boundA t) n) = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hw
  have ck := F.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 := hX2.2.2.1
  have hAI3 : ActIdle σ' := F.actIdle J.act
  -- the dead set without the thread and the notification
  set D' : Set U64 := {q | q ∈ D ∧ q ≠ t ∧ q ≠ n} with hD'
  have hdead : ∀ q ∈ D', DeadP (L := L) H (L.wr (L.wr s (nBoundA n) t) (P1.boundA t) n) q := by
    intro q hq
    have hqt : q.bv ≠ t.bv := fun e => hq.2.1 (P1.eq_of_bv e)
    have hqn : q.bv ≠ n.bv := fun e => hq.2.2 (P1.eq_of_bv e)
    have ek : σ'.kheap q.bv = σ.kheap q.bv := by
      simp [hσ', Notif.updK, hqt, hqn]
    refine J.deadP_keep hS3 hX2.1 (fun y hy _ => ⟨y, by rw [ek]; exact hy, rfl, rfl, Or.inl rfl⟩)
      (fun y hy => by rw [ek]; exact hy) (fun y hy => ⟨y, by rw [ek]; exact hy, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun y hy => ⟨y, by rw [ek]; exact hy, rfl⟩) (fun y m hy => ⟨y, by rw [ek]; exact hy, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.finW_scOut hw hz hqC hK8 hK) rfl hAI3.1
      (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) (J.jcov.dead q hq.1)
  -- `JCovD` with the new dead set
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hJ0 : JCovD (L := L) Z.th H Z.G D' Cs s := by
    refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q hq => J.jcov.dead q hq.1, J.jcov.ks, J.jcov.idleOut⟩
    · rcases J.jcov.th q k hq with hc | hd | hi
      · exact Or.inl hc
      · by_cases e1 : q = t
        · subst e1; exact Or.inl (cT1 k hq)
        · by_cases e2 : q = n
          · subst e2; exact Or.inl (cN1 k hq)
          · exact Or.inr (Or.inl ⟨hd, e1, e2⟩)
      · exact Or.inr (Or.inr hi)
    · rcases J.jcov.h q k hq with hc | hd | hi
      · exact Or.inl hc
      · by_cases e1 : q = t
        · subst e1; exact Or.inl (cT2 k hq)
        · by_cases e2 : q = n
          · subst e2; exact Or.inl (cN2 k hq)
          · exact Or.inr (Or.inl ⟨hd, e1, e2⟩)
      · exact Or.inr (Or.inr hi)
  have hidl := J.idleW_keep hS3 F.idle F.isc
  have hjc : JCovD (L := L) Z.th H Z.G D' Cs (L.wr (L.wr s (nBoundA n) t) (P1.boundA t) n) := by
    exact hJ0.same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq (L.wr (L.wr s (nBoundA n) t) (P1.boundA t) n) σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y m _ hq => F.szKeep q.bv y m hq) hks (J.finW_irq hw) hidl.2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.ct F.csc (fun sl h => Or.inl (by rw [← F.orig]; exact h))
    (by rw [F.arch])
    (fun q ao h => (F.oth (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hDbg (D' := D')
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D' (L.wr (L.wr s (nBoundA n) t) (P1.boundA t) n) σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjc, hkern,
      J.finW_utc hw hF.1 F.cdt F.orig F.arch hDbg, F.nsc J.nsc, I3, F.cur J.cur, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa, F.isorted J.isorted, F.curRunM J.curRun, hblk0⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') (L.wr (L.wr s (nBoundA n) t) (P1.boundA t) n) σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, D', J.cs_frameI hks hX3 hw (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) F.arch (fun q ao h => (F.oth (fun _ e => by cases e) (fun _ e => by cases e)).2 h) F.szKeep hF.1 F.kback F.ipcFr hC R hKd hck.orig hidl.1
    (fun p hp => ⟨J.zD p hp, fun e => J.not_ztcb hxT (fun _ _ _ h => by rw [capV_of_capAt hcT] at h; cases h)
      (by rw [capV_of_capAt hcT, e]; simp [absCap, Fl4Spec.objRefs]) hp, fun e => by
        have h1 : H p = some .tcb := J.zH.1 p (J.thT p (J.ztcb_tcb hp))
        rw [e, J.zH.2.2.2 n hn] at h1; cases h1⟩)⟩

end

end

end Fl4Proofs.P3
