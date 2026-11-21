/-
P3 (DESIGN.md §9), CSpace: **the inactive SC at `J`** (the last step of a
final SC cap's finalisation, XTopJointFinSc's `JAtZ.finScJ`):
`REFILL_MAX` and `SPORADIC` of an SC cleared, against the spec's
`sched_context_set_inactive`, from `JAtZ` to `JAtZ` (`JAtZ.setInactiveJ`).

The SC's thread, notification and reply words are null (the earlier
unbinds). The spec side (`Sched.InactOK`): only the SC changes, no thread is
bound to it (`Inv.back`) and its call stack is empty (`CallRel`: the `REPLY`
word heads it, a reply is never null), so `Inv`, `CurInv`, `CurOwnW`,
`OffOK`, `ActIdle`, `BlockedScActive` and `CurRunM` are kept although the SC
becomes inactive. The SC may be the current SC (the current thread deleting
the last cap to its own SC): `CurInv` then cannot hold (its current thread
is bound to the current SC, `Inv.back`), so a reschedule is pending
(`JAtZ.cur`); `CurOwnW` holds unowned, and `OffOK` asks nothing of an
inactive current SC other than the idle SC. FL4's side: XTop's
`SchedRel.set_inactive`, `xtop_sc_step`; the call stacks, yield and MCP
words by `ScAll.of_k` (`Pres` of the spec step); `JAtZ.sc_frame` for the
rest, P1's `BlkOK` by `deact_all` (the SC leaves the active set), the dead
set kept (the SC's link words are untouched, `deadP_sc_step` elsewhere).
-/
import Fl4Proofs.P3.XTopJointFinThread
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

section Spec

theorem scActive_inact (x : SchedContext) : scActive (inactSc x) = false := rfl

/-- The SC `p` made inactive: no thread bound to it, an empty call stack. -/
structure InactOK (σ : State Unit) (p : ObjRef) (y : SchedContext) (m : Nat) : Prop where
  hk : σ.kheap p = some (.schedContext y m)
  tcb : y.scTcb = none
  rep : y.scReplies = []

variable {σ : State Unit} {p : ObjRef} {y : SchedContext} {m : Nat}

theorem InactOK.ko (h : InactOK σ p y m) {q : ObjRef} (hq : q ≠ p) :
    (updSc σ p (inactSc y) m).kheap q = σ.kheap q := by
  simp [updK, hq]

theorem InactOK.ne_tcb (h : InactOK σ p y m) {q : ObjRef} {x : Tcb} (hq : σ.kheap q = some (.tcb x)) : q ≠ p := by
  rintro rfl; rw [h.hk] at hq; cases hq

theorem InactOK.tcb' (h : InactOK σ p y m) {q : ObjRef} {x : Tcb} :
    (updSc σ p (inactSc y) m).kheap q = some (.tcb x) ↔ σ.kheap q = some (.tcb x) := by
  by_cases e : q = p
  · subst e; simp [updK, h.hk]
  · rw [h.ko e]

theorem InactOK.kcs (h : InactOK σ p y m) (hcsc : p ≠ σ.curSc) :
    (updSc σ p (inactSc y) m).kheap (updSc σ p (inactSc y) m).curSc = σ.kheap σ.curSc :=
  h.ko (Ne.symm hcsc)

/-- No thread is bound to the SC (`Inv.back`). -/
theorem InactOK.nb (h : InactOK σ p y m) (hI : Inv σ) {u : ObjRef} {x : Tcb} (hx : σ.kheap u = some (.tcb x)) :
    x.tcbSchedContext ≠ some p := by
  intro e
  obtain ⟨y', n', hy', ht⟩ := hI.back u x p hx e
  rw [h.hk] at hy'; cases hy'
  rw [h.tcb] at ht; cases ht

theorem InactOK.inv (h : InactOK σ p y m) (hI : Inv σ) : Inv (updSc σ p (inactSc y) m) := by
  have nb : ∀ {u : ObjRef} {x : Tcb}, σ.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p :=
    fun hx => h.nb hI hx
  -- a thread's SC is kept
  have scK : ∀ u x q y' n, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some q →
      ((updSc σ p (inactSc y) m).kheap q = some (.schedContext y' n) ↔ σ.kheap q = some (.schedContext y' n)) :=
    fun u x q y' n hx hq => by
      have : q ≠ p := fun e => nb hx (e ▸ hq)
      rw [h.ko this]
  have rtq : ∀ u ∈ σ.releaseQueue, specRt (updSc σ p (inactSc y) m) u = specRt σ u := by
    intro u hu
    obtain ⟨x, scp, y', n, h1, h2, -, h4, h5⟩ := hI.rel u hu
    rw [specRt_eq (h.tcb'.2 h1) h2 ((scK u x scp y' n h1 h2).2 h4) (hI.ne _ _ _ h4 h5),
      specRt_eq h1 h2 h4 (hI.ne _ _ _ h4 h5)]
  have inact : ∀ q y' n, (updSc σ p (inactSc y) m).kheap q = some (.schedContext y' n) → scActive y' = true →
      σ.kheap q = some (.schedContext y' n) := by
    intro q y' n hq ha
    by_cases e : q = p
    · subst e; simp [updK] at hq; obtain ⟨rfl, -⟩ := hq; rw [scActive_inact] at ha; cases ha
    · rwa [h.ko e] at hq
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun q y' n hy ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q y' n hy ha => ?_, fun q y' n hy ha hp0 => ?_⟩
  · obtain ⟨x, scp, y', n, h1, h2, h3, h4, h5⟩ := hI.rq d q u hu
    exact ⟨x, scp, y', n, h.tcb'.2 h1, h2, h3, (scK u x scp y' n h1 h2).2 h4, h5⟩
  · obtain ⟨x, scp, y', n, h1, h2, h3, h4, h5⟩ := hI.rel u hu
    exact ⟨x, scp, y', n, h.tcb'.2 h1, h2, h3, (scK u x scp y' n h1 h2).2 h4, h5⟩
  · exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab => by rw [rtq a ha, rtq b hb]; exact hab) hI.sorted
  · have hx0 := h.tcb'.1 hx
    intro x' scp y' n h1 h2 h3 h4 h5
    have h1' := h.tcb'.1 h1
    exact hI.rd u x hx0 hc x' scp y' n h1' h2 ((scK u x' scp y' n h1' h2).1 h3) h4 h5
  · exact hI.refills q y' n (inact q y' n hy ha) ha
  · have hx0 := h.tcb'.1 hx
    obtain ⟨y', n, h1, h2⟩ := hI.back u x q hx0 hq
    exact ⟨y', n, (scK u x q y' n hx0 hq).2 h1, h2⟩
  · have hq0 : q ≠ p := by rintro rfl; simp [updK] at hx
    rw [h.ko hq0] at hx
    obtain ⟨y', n, h1⟩ := hI.ntfnSc q x q' hx hq
    by_cases e : q' = p
    · subst e; exact ⟨inactSc y, m, by simp [updK]⟩
    · exact ⟨y', n, by rw [h.ko e]; exact h1⟩
  · exact hI.ne q y' n (inact q y' n hy ha) ha
  · exact hI.rr q y' n (inact q y' n hy ha) ha hp0

/-- A thread bound to an SC is bound to an SC other than `p` (`Inv.back`). -/
theorem InactOK.ne_of_bound (h : InactOK σ p y m) (hI : Inv σ) {u : ObjRef} {x : Tcb} {q : ObjRef}
    (hx : σ.kheap u = some (.tcb x)) (hq : x.tcbSchedContext = some q) : p ≠ q :=
  fun e => h.nb hI hx (e ▸ hq)

theorem InactOK.curInv (h : InactOK σ p y m) (hI : Inv σ) (hC : CurInv σ) : CurInv (updSc σ p (inactSc y) m) := by
  obtain ⟨xt, hkt, hsc, hnb⟩ := hC.tcb
  have hcsc := h.ne_of_bound hI hkt hsc
  obtain ⟨y0, n0, hy0⟩ := hC.sc
  refine ⟨⟨xt, h.tcb'.2 hkt, hsc, hnb⟩, ⟨y0, n0, by rw [h.kcs hcsc]; exact hy0⟩, fun hid y' n hy => ?_,
    hC.notRel⟩
  rw [h.kcs hcsc] at hy
  exact hC.active hid y' n hy

theorem InactOK.own {T C : Set U64} (h : InactOK σ p y m) (hI : Inv σ) (hO : CurOwnW T C σ) :
    CurOwnW T C (updSc σ p (inactSc y) m) := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · have hcsc := h.ne_of_bound hI hkt hxs
    exact Or.inl ⟨u, hu, xt, h.tcb'.2 hkt, hxs, fun x n hx => hown x n (by rwa [h.kcs hcsc] at hx), hnr⟩
  · refine Or.inr ⟨hcs, fun x n hx => ?_⟩
    by_cases hcsc : p = σ.curSc
    · subst hcsc
      simp [updK] at hx
      obtain ⟨rfl, -⟩ := hx
      exact h.tcb
    · exact hun x n (by rwa [h.kcs hcsc] at hx)

theorem InactOK.off (h : InactOK σ p y m) (hpi : p ≠ σ.idleSc) (hO : OffOK σ) :
    OffOK (updSc σ p (inactSc y) m) := by
  intro hpos y' n hy ha
  by_cases hcsc : p = σ.curSc
  · subst hcsc
    simp [updK] at hy
    obtain ⟨rfl, -⟩ := hy
    exact absurd ((scActive_inact y).symm.trans (ha hpi)) Bool.false_ne_true
  · rw [h.kcs hcsc] at hy
    exact hO hpos y' n hy ha

theorem InactOK.sched (h : InactOK σ p y m) (hI : Inv σ) {t : ObjRef} (hs : schedulable t σ = true) :
    schedulable t (updSc σ p (inactSc y) m) = true := by
  obtain ⟨x, scp, y', n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv hs
  have hne : scp ≠ p := fun e => h.nb hI h1 (e ▸ h2)
  exact schedulable_of (h.tcb'.2 h1) h2 h3 (by rw [h.ko hne]; exact h4) h5 h6

theorem InactOK.actIdle (h : InactOK σ p y m) (hI : Inv σ) (hA : ActIdle σ) :
    ActIdle (updSc σ p (inactSc y) m) := by
  obtain ⟨hS, x, h1, h2, h3, h4⟩ := hA
  exact ⟨fun t ht => h.sched hI (hS t ht), x, h.tcb'.2 h1, h2, h3, h4⟩

theorem InactOK.bsa (h : InactOK σ p y m) (hB : BlockedScActive σ) :
    BlockedScActive (updSc σ p (inactSc y) m) := by
  refine ⟨fun q y' n t x hq hyt hx hqs => ?_, fun q y' n hq hr => ?_⟩
  · by_cases e : q = p
    · subst e; simp [updK] at hq; obtain ⟨rfl, -⟩ := hq
      have : (inactSc y).scTcb = y.scTcb := rfl
      rw [this, h.tcb] at hyt; cases hyt
    · rw [h.ko e] at hq
      exact hB.tcb q y' n t x hq hyt (h.tcb'.1 hx) hqs
  · by_cases e : q = p
    · subst e; simp [updK] at hq; obtain ⟨rfl, -⟩ := hq
      exact absurd h.rep hr
    · rw [h.ko e] at hq
      exact hB.replies q y' n hq hr

theorem InactOK.curRun (h : InactOK σ p y m) (hR : CurRunM σ) : CurRunM (updSc σ p (inactSc y) m) := by
  rcases hR with e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl fun x hx => e x (h.tcb'.1 hx))
  · exact Or.inr (Or.inr e)

theorem pres_schedContextSetInactive (f : Bool × Bool) (p : ObjRef) :
    Pres f (schedContextSetInactive (Z := Unit) p) := by
  unfold schedContextSetInactive; pres_auto

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **The inactive SC at `J`** (module docstring): XTopJointFinSc's
a step of XTopJointFinSc's `JAtZ.finScJ`, proved. -/
theorem JAtZ.setInactiveJD {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64)
    (hpi : p.bv ≠ σ.idleSc) (t0 : L.mem s (P1.scTcbA p) = 0#u64)
    (n0 : L.mem s (P1.scNtfnA p) = 0#u64) (r0 : L.mem s (P1.scReplyA p) = 0#u64) :
    ∃ σ', Fl4Spec.schedContextSetInactive (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      JTPD (L := L) arI AR Z H Cs D (L.wr (L.wr s (maxA p) 0#u64) (scW p 64#u64) 0#u64) a σ' := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs p hpC
  obtain ⟨hS6, hFE, hKV, hw6⟩ := hS.set_inactive hpC hk hpi
  have hR6 := hR.frame hS.placed hFE hKV
  have he5 := setInactive_eq hk
  refine ⟨_, he5, ?_⟩
  have hK6 : ScTKw (fun _ => False) σ (updSc σ p.bv (inactSc x) n) :=
    nkt_schedContextSetInactive p.bv σ ((), _) (by rw [he5]; exact Set.mem_singleton _)
  have hWK : P1.WritesIn st s (L.wr (L.wr s (maxA p) 0#u64) (scW p 64#u64) 0#u64)
      (KFoot st Z.T Z.N Z.C Z.c s σ) := by
    refine hw6.mono fun b hb => KFoot.of_sw ?_
    rcases hb with rfl | rfl
    · exact sw_hdr hS hpC (K := 72#u64) (by simp) (by simp) (by decide)
    · exact sw_hdr hS hpC (K := 64#u64) (by simp) (by simp) (by decide)
  have hW6 : P1.WritesIn st s (L.wr (L.wr s (maxA p) 0#u64) (scW p 64#u64) 0#u64)
      (TFoot st Z.T Z.N Z.C Z.c s σ) := hWK.mono fun b hb => Or.inl hb
  have hX' := xtop_sc_step (ct := σ.curThread) J.xtop J.ip J.nk hW6 (hK6.mono fun _ h => h.elim) hS6 hR6 id
  -- the spec side
  have hrep : x.scReplies = [] := by
    obtain ⟨⟨y1, n1, hk1, hy1⟩, hLR, -, hSW⟩ := J.call.stack p hpC
    rw [hk] at hk1; cases hk1
    rw [hy1]
    cases e : Lst p with
    | nil => rfl
    | cons r rest =>
      exfalso
      have hr : L.mem s (scReplyA p) = r := by have h1 := hSW.1; rw [e] at h1; exact h1
      have hrR : r ∈ Z.R := hLR r (by rw [e]; simp)
      have hH := J.zH.2.2.1 r hrR
      have : r = 0#u64 := by rw [← hr]; exact r0
      rw [this, J.kern.h0] at hH; cases hH
  have hO : InactOK σ p.bv x n := ⟨hk, by rw [hx.tcb, ← scTcbA_eq, t0, Notif.optRef_zero], hrep⟩
  have hI' := hO.inv J.inv
  have hSOK : SOK (true, true) σ (updSc σ p.bv (inactSc x) n) :=
    Pres.of_eq (pres_schedContextSetInactive (true, true) p.bv) he5
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS6, hR6, J.nsc.updSc, hI'⟩, hWK, hSOK⟩
  have hact' := hO.actIdle J.inv J.act
  -- the dead set: no link changes
  have hL : LK (fun _ => False) σ (updSc σ p.bv (inactSc x) n) := fun q => Or.inr (by
    by_cases e : q = p.bv
    · subst e
      rw [hk, show (updSc σ p.bv (inactSc x) n).kheap p.bv = some (.schedContext (inactSc x) n) by simp [updK]]
      exact LObj.sc (Or.inl rfl) (Or.inl rfl)
    · rw [hO.ko e]; exact OL.refl _)
  have hF : Sched.FK σ (updSc σ p.bv (inactSc x) n) := ⟨rfl, rfl, rfl⟩
  have hDead : ∀ q ∈ D, DeadP (L := L) H (L.wr (L.wr s (maxA p) 0#u64) (scW p 64#u64) 0#u64) q := fun q hq =>
    J.deadP_sc_step hX' hW6 hK6 (fun _ _ h _ => h.elim) hL hF hact'.1 hY' ((hSOK.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  -- P1
  have hpS : p ∈ P1.Heap.scs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨_, (hJ.sc p x n hp0 hk).2⟩
  have hX4 := J.blk.2.2.1
  have hT4 := J.blk.1.choose_spec.choose_spec.tcbs
  have hnbW : ∀ y ∈ P1.Heap.tcbs H, L.mem s (P1.scA y) ≠ p := fun y hy e => by
    obtain ⟨-, e2, -⟩ := hX4.2.2.bound y hy (by rw [e]; exact hp0)
    rw [e, t0] at e2
    exact (hT4 y hy).ne0 (by rw [← e2]; rfl)
  have hnnW : ∀ m ∈ P1.Heap.ntfns H, L.mem s (P1.ntfnScA m) ≠ p := fun m hm e => by
    obtain ⟨-, e2⟩ := hX4.2.2.nsc m hm (by rw [e]; exact hp0)
    rw [e, n0] at e2
    exact hX4.1.nt0 m hm e2.symm
  have esp : core.num.U64.wrapping_add p layout.sc.SPORADIC = scW p 64#u64 := by
    unfold scW layout.sc.SPORADIC; rfl
  obtain ⟨hblk', hfoot⟩ := P1.deact_all J.blk hpS hnbW hnnW r0
  rw [esp] at hblk' hfoot
  have hDbg := J.kw_dbg (hfoot.mono (Set.empty_subset _))
  have hKd := J.kw_dbgKeep (hfoot.mono (Set.empty_subset _))
  exact ⟨Z.vs, Ac \ {p}, Lst', J.sc_frame hW6 hK6 hX' hCR' hRF' hY' hM' (J.sc_buf hW6 hK6) hRP'
    (J.sc_apart hW6 hK6) (J.sc_jpl hW6 hK6 (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hW6 hDead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2))
    (J.sc_kern hW6 hK6 hF hX' hDbg fun _ h => h) (J.sc_utc hW6 hK6 hDbg) J.nsc.updSc hI'
    (J.cur.imp id (hO.curInv J.inv)) (hO.own J.inv J.own) (hO.off hpi J.off) hact' (hO.bsa J.bsa) (hO.curRun J.curRun) hblk' hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩


set_option maxHeartbeats 4000000 in
/-- `JAtZ.setInactiveJD` with the dead set existential. -/
theorem JAtZ.setInactiveJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64)
    (hpi : p.bv ≠ σ.idleSc) (t0 : L.mem s (P1.scTcbA p) = 0#u64)
    (n0 : L.mem s (P1.scNtfnA p) = 0#u64) (r0 : L.mem s (P1.scReplyA p) = 0#u64) :
    ∃ σ', Fl4Spec.schedContextSetInactive (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      JTP (L := L) arI AR Z H Cs (L.wr (L.wr s (maxA p) 0#u64) (scW p 64#u64) 0#u64) a σ' :=
  let ⟨σ', he, V, Ac', Lst', J'⟩ := J.setInactiveJD arI hpC hp0 hpi t0 n0 r0; ⟨σ', he, V, Ac', Lst', D, J'⟩

end

end

end Fl4Proofs.P3
