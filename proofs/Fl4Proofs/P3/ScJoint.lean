/-
P3 (DESIGN.md §9), scheduling contexts: **the SC family's leaves on `JAt`**
(the fold's re-scoping, plan §0): each producer takes `JAtZ` at its start
state in place of its bundles (`XTopAt`, `ScExtra`, `UtP3Ok`), through
`JointAt`'s projections.

* `decode_invocation_sched_controlJAt`, `decode_invocation_sched_contextJAt`:
  the SchedControl and SchedContext caps, `JAt` before ⇒ `XTop` after; the
  current thread's TCB and its runnability come from `JAtZ` (`curTcb`,
  `curRun`). The platform facts stay [global] premises.
* `UtJOk`: P1's `P3Ok` for the untyped retype as `JAt` at the decode's start
  with the invoked slot's facts; `RegionUnrefJ`: `RegionUnref` over `JAtZ`;
  `utRetypeP3_ofJ`: P1's `UtRetypeP3` at `UtJOk` (`utRetypeP3_gen`).
-/
import Fl4Proofs.P3.JointAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- The current thread of a `JAtZ` state: the node's `CUR_THREAD` word, the
spec's, a TCB. -/
theorem JAtZ.curEq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    σ.curThread = ct.bv ∧ ∃ x, σ.kheap ct.bv = some (.tcb x) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  obtain ⟨-, x, hk⟩ := J.xtop.curTcb hcur
  exact ⟨hcur, x, hk⟩

/-- The current thread of a `JAtZ` state at a system call (not the idle
thread): `curEq`, and the TCB runnable (`CurRunW.run`). -/
theorem JAtZ.curRunnable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    σ.curThread = ct.bv ∧ ∃ x, σ.kheap ct.bv = some (.tcb x) ∧ Fl4Spec.runnable x.tcbState = true := by
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  exact ⟨hcur, x, hk, J.curRun.run hni x (by rw [hcur]; exact hk)⟩

/-- **The SchedControl cap on `JAt`** (`decode_invocation_sched_controlXT`). -/
theorem decode_invocation_sched_controlJAt {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (hres : σ.schedulerAction ≠ .chooseNewThread)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hcpu : cpu = Z.c) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hsb : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (hsc : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ Z.C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ Z.T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄) :
    DecOKDMX (L := L) arI (XTop (L := L) AR) s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer := by
  obtain ⟨-, xc, hkc, hrun⟩ := J.curRunnable hni hct
  exact decode_invocation_sched_controlXT s a σ J.xtop (J.scExtra hres htm hmb hmax htu hmsg) lbl slbl hlbl cpu length
    buf ct hcpu hct args hlen hargs extra x0 hx0 excaps hex hsb hsc hkc hrun slot blk call don fp ci sl buffer hArch

/-- **The SchedContext cap on `JAt`** (`decode_invocation_sched_contextXT`). -/
theorem decode_invocation_sched_contextJAt {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction ≠ .chooseNewThread)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ Fl4Spec.idleScPtr)
    (hl : lbl = fl4_abi.label.SchedContextBind ∨ lbl = fl4_abi.label.SchedContextUnbindObject ∨
      (lbl = fl4_abi.label.SchedContextYieldTo ∧ L.mem s (P1.scYieldFromA sc) = 0#u64))
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ Z.N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄) :
    DecOKDMX (L := L) arI (XTop (L := L) AR) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ∨
    DecOKRMX (L := L) arI (fun _ _ _ => True) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  have hcapT : x0 ≠ 0#u64 → ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ Z.T := by
    intro hx p hc
    rcases hex with ⟨h0, -⟩ | ⟨-, -, c, a', rest, hc', -, hv, -⟩
    · exact absurd h0 hx
    · rw [hc] at hc'; cases eq_of_ok_eq hc'
      exact J.thT p hv
  have hcapN : x0 ≠ 0#u64 → ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ Z.N ∧ p ≠ 0#u64 := by
    intro hx p b w r hc
    rcases hex with ⟨h0, -⟩ | ⟨-, hS, -⟩
    · exact absurd h0 hx
    · obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hH : H p = some .ntfn := ((hJ.typed x0 hS).2.1 p b w r (capV_of_capAt hc)).2
      refine ⟨J.hset.2.1 p hH, fun e => ?_⟩
      rw [e, J.kern.h0] at hH; cases hH
  exact decode_invocation_sched_contextXT s a σ J.xtop (J.scExtra hres htm hmb hmax htu hmsg) lbl slbl hlbl sb hsc hpi hl hback
      hbn hct hcs extra x0 hx0 excaps hex hcapT hcapN length slot buf blk call don fp args ci sl buffer hArch

/-! ## The untyped retype on `JAt` -/

/-- **P1's `P3Ok` on `JAt`**: the joint invariant at the decode's start
(over P1's heap `H` and cores `Cs`), and the invoked slot a CNode slot of
the typed heap holding the cap, the extra caps related. -/
def UtJOk (arI : machine.Arch A) (H : P1.Heap) (Cs : Set U64) (s : S) (slot : U64) (cap : capability.Cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  ∃ (AR : A → Fl4Spec.Cr3 → Prop) (a : A) (σ : Fl4Spec.State Unit) (Z : XSets) (Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (pp : U64) (rs : Nat) (idx : List Bool),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ Z.th pp = some (.cnode rs) ∧ idx.length = rs ∧
      slot = cslotAddr (pp.bv, idx) ∧ capAt (L.mem s) slot = ok cap ∧
      ∀ x ∈ extra.val, x ≠ 0#u64 → ∃ c a, capAt (L.mem s) x = ok c ∧ CapRel c a ∧ CapValid Z.th c

/-- **[J] `RegionUnref` on `JAt`** (`RegionUnref`'s docstring): after the
restart from a `JAt` state, the kept objects' links and FL4's timer and
debug lists name no object of a dead range. -/
def RegionUnrefJ (arI : machine.Arch A) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s0 s : S)
    (a : A) (σ : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a σ →
    sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s →
    ∀ lo hi : Nat, (∀ q k, H q = some k → P1.RegionD H lo hi q → q ∈ D) →
      KeptRefsP3 (L := L) H (P1.RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (P1.RegionD H lo hi) Cs s

theorem utOkRU_J {H : P1.Heap} {Cs : Set U64} (hRU : RegionUnrefJ (L := L) arI H Cs) :
    UtOkRU (L := L) arI H Cs (UtJOk (L := L) arI H Cs) := by
  rintro s0 s slot cap extra ⟨AR, a, σ, Z, Ac, Lst, D, pp, rs, idx, J, hn, hi, hsl, hc, hx⟩ hrs
  exact ⟨Z.th, Z.G, D, σ, pp, rs, idx, J.utJoint hn hi hsl hc hx, hRU AR Z Ac Lst D s0 s a σ J hrs⟩

/-- **P1's `UtRetypeP3` at `UtJOk`** (`utRetypeP3_gen`): `JAt` at the
decode's start ⇒ the retype's `CreateOK` (P1's kernel entry). Named:
`RegionUnrefJ` [J], the new TCBs' debug links and the VT-x types at
`UtJOk`. -/
theorem utRetypeP3_ofJ [Fl4Proofs.P1.PlainStore st] (arI : machine.Arch A) (hA : P0.ArchTotal arI) (H : P1.Heap) (Cs U : Set U64)
    (Adm : P1.PSets → Prop) (hAdm : ∀ H' : P1.Heap, P1.HeapOK H' → H' 0#u64 = none → Adm (P1.PSets.ofHeap H'))
    (h0Cs : 0#u64 ∈ Cs) (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hRU : RegionUnrefJ (L := L) arI H Cs) (hDbg : UtDbgTcbP (L := L) arI H Cs (UtJOk (L := L) arI H Cs))
    (hVtx : UtVtxP (L := L) arI H Cs U (UtJOk (L := L) arI H Cs)) :
    P1.UtRetypeP3 st arI Adm H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits U
      (UtJOk (L := L) arI H Cs) :=
  utRetypeP3_gen arI hA H Cs U Adm hAdm h0Cs hrcb hppS _ (utOkRU_J hRU) hDbg hVtx

end

end

end Fl4Proofs.P3
