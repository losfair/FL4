/-
P3 (DESIGN.md §9), CSpace and IPC: **a notification cap's deletion keeps
`JAtZ`** (`JStepHyps.del`): FL4's `delete_one` of a notification cap in a
CNode's slot is the notification's finalisation when final (`finNtfnJ`,
XTopJointFin), then `empty_slot` with a null cleanup, a CNode-only slot step
whose dead set grows by the notification when its last cap goes.

* `emptySlot_null_nko`, `emptySlot_null_nkz`: the spec's `empty_slot` with a
  null cleanup changes the slot's CNode only and keeps the objects' kinds.
* `JAtZ.deadP_slot`: the dead stay dead across a CNode-only slot step.
* `jowes_slotD`: `jowes_slotOf` with the dead set and the untyped caps' facts
  after given (the dead set may grow).
-/
import Fl4Proofs.P3.XTopJointFin
import Fl4Proofs.P3.XTopDelOne
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section Spec
open Fl4Spec

/-- **`empty_slot` with a null cleanup changes the slot's object only.** -/
theorem emptySlot_null_nko (sl : CslotPtr) : NKO {sl.1} (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot setCdt setOriginal postCapDeletion
  repeat (first | exact nko_getCap _ | exact nko_setCap _ _ (by simp) | exact nko_doExtendedOp _ |
    exact nko_pure _ | exact nko_pure' _ | exact nko_fail | exact nko_gets _ | exact nko_get |
    exact nko_assert _ | exact nko_get_put (fun σ => rfl) |
    exact nko_modify (fun σ => rfl) | (refine nko_bind ?_ (fun _ => ?_)) |
    (apply nko_ite) | split)

/-- **`empty_slot` with a null cleanup keeps the objects' kinds.** -/
theorem emptySlot_null_nkz (sl : CslotPtr) : NKZ (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot setCdt setOriginal postCapDeletion
  repeat (first | exact nkz_getCap _ | exact nkz_setCap _ _ | exact nkz_doExtendedOp _ |
    exact nkz_pure _ | exact nkz_pure' _ | exact nkz_fail | exact nkz_gets _ | exact nkz_get |
    exact nkz_assert _ | exact nkz_get_put (fun σ => rfl) |
    exact nkz_modify (fun σ => rfl) | (refine nkz_bind ?_ (fun _ => ?_)) |
    (apply nkz_ite) | split)

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The dead stay dead across a CNode-only slot step** (`deadP_hstep` at
the sets `Z.mv G' V'`). -/
theorem JAtZ.deadP_slot {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {G' : MdbGhost} {V' : XVs} (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ')
    (hcn : Ipc.CnK σ σ') (hkc : KeepCT σ σ') (hw : P1.WritesIn st s s' (InSlot Z.th))
    {q : U64} (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q := by
  have hC := CnStep.of_cnK hcn
  obtain ⟨-, -, -, k3, -⟩ := inSlot_keeps arI J hw
  exact J.deadP_keep hX'.fin.1.1.1 hX'.ipc (fun x hx _ => let ⟨y, hy, hc⟩ := hC.tcbF hx; ⟨y, hy, hc.st, hc.ntfn, Or.inl hc.sc⟩)
    (fun x hx => (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx)
    (fun x hx => ⟨x, hC.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx, rfl⟩)
    (fun x n hx => ⟨x, hC.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (fun hqC => k3 q hqC)
    (fun z hz _ K h8 hK => J.inSlot_scKeep hw hz h8 hK) hC.idle (J.act.cn hC).1 hd

set_option maxHeartbeats 4000000 in
/-- **A CNode-only slot step's `JCs` and `JRest`** (`jowes_slotOf` with the
dead set `D'` and its `JCovD`, and the untyped caps' facts after, given). -/
theorem jowes_slotD {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {G' : MdbGhost} {V' : XVs} (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ')
    (hcn : Ipc.CnK σ σ') (hkc : KeepCT σ σ') (hw : P1.WritesIn st s s' (InSlot Z.th))
    {kb : U64} (hFI : FinInv Z.th (L.mem s') σ' G') (hMO : MdbOKV kb (L.mem s') G') (hkz : KSz σ σ')
    (hTK : TypedKept Z.th (L.mem s) (L.mem s'))
    (hT3 : ∀ t, Z.th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3) ∨
      capV (L.mem s') (slotOf t 3) = .Null)
    (hDl : DelInv Z.th (L.mem s')) (hUK : UtKept Z.th (L.mem s) (L.mem s'))
    {D' : Set U64} (hjc : JCovD (L := L) Z.th H G' D' Cs s') (hcl : L.cscW s ∉ D')
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl)
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi) :
    JCs (L := L) (Z.mv G' V') s' σ' ∧ JRest (L := L) arI (Z.mv G' V') H Cs Ac Lst D' s' σ' := by
  have hC := CnStep.of_cnK hcn
  obtain ⟨k1, k2, kb', k3, k4⟩ := inSlot_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := by
    have hPl := J.xtop.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    exact (P1.blk_of_capw J.blk hw' (J.slotCapW P1.tlow_slots)).1
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    let ⟨Tr, Cq, hJ⟩ := J.jpl
    ⟨Tr, Cq, hJ.slotT hkc hw.1 J.intL hTK hT3⟩
  obtain ⟨-, ⟨-, -, hM', -, -⟩, -⟩ := hX'.rel
  have hJC0 := J.jcs_slot hM' hMO hFI hUK hkz hDl
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hC.ct hC.csc horig hgp
    (fun p ao h => (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 h) hDbg (D' := D') hcl
  exact ⟨⟨hJC0.del, hJC0.ut, hJC0.finM, hJC0.sfree⟩, ⟨hCR', hRF', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb' (fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.buf⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_keepCT hkc), hjpl,
    hjc, hkern, hutc, J.nsc.cn hC.toHStep, J.inv.cn hC, CurInvW.cn J.cur hC, J.own.cn hC.toHStep, J.off.cn hC.toHStep,
    J.act.cn hC,
    J.bsa.cn hC.toHStep, J.isorted.cn hC.toHStep, J.curRun.cn hC.toHStep (Or.inr hC.act), hblk⟩⟩

/-- **What a deletion cannot re-establish of an untyped cap** [J]: an untyped
cap left childless by the deletion (the deleted cap its only child, itself
childless) has no MDB slot and no CNode in its region and the original caps
in its region, as `UtCapP3`'s childless clauses (`ns`, `rst`) need (l4v
`valid_untyped`'s `descendants_range_in`: the objects of a region are named
by the region's descendants only). -/
def DelUtFact (th : TypedHeap) (s' : S) (σ' : Fl4Spec.State Unit) (p sb fi : U64) : Prop :=
  (∀ y, IsSlot th y → capV (L.mem s') y ≠ .Null → y.val < p.val ∨ p.val + 2 ^ sb.val ≤ y.val) ∧
  (fi.val ≠ 0 →
    (∀ sl, σ'.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
    (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
    ¬ (p.val ≤ (L.mem s' (L.nodeAt s' 0#u64 layout.node.DEBUG_TCBS)).val ∧
      (L.mem s' (L.nodeAt s' 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))

set_option maxHeartbeats 4000000 in
/-- **The untyped caps' facts after emptying a slot** (`ins_utc`'s argument):
the caps other than the emptied slot's kept, its cap null after; a
childless untyped cap after was childless before, or is the deleted cap's
parent left childless (`DelUtFact`, named). -/
theorem JAtZ.del_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {sl : Fl4Spec.CslotPtr}
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y)
    (hnull : capV (L.mem s') (cslotAddr sl) = .Null)
    (hw : P1.WritesIn st s s' (InSlot Z.th))
    (hcdt : σ'.cdt = Function.update (fun x => if σ.cdt x = some sl then σ.cdt sl else σ.cdt x) sl none)
    (horig : ∀ sl', σ'.isOriginalCap sl' = true → σ.isOriginalCap sl' = true)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4) (hM' : MdbLinks Z.th (L.mem s') G')
    (hUt : ∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
      σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
      DelUtFact (L := L) Z.th s' σ' up usb ufi) :
    ∀ u p sb fi dev, AbsSlot Z.th u → capAt (L.mem s') (cslotAddr u) = ok (.Untyped p sb fi dev) →
      UtCapP3 (L := L) arI Z.th s' σ' G' u p sb fi := by
  intro u p sb fi dev hu hcap'
  obtain ⟨hP, ⟨-, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hne : cslotAddr u ≠ cslotAddr sl := fun e => by
    have := capV_of_capAt hcap'; rw [e, hnull] at this; cases this
  have hune : u ≠ sl := fun e => hne (by rw [e])
  have hcv : capV (L.mem s) (cslotAddr u) = .Untyped p sb fi dev := by
    rw [← hcap _ hu.isSlot hne]; exact capV_of_capAt hcap'
  have hcap0 : capAt (L.mem s) (cslotAddr u) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc u p sb fi dev hu hcap0
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hfi := U.fiLe
  have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, i, hi, rfl⟩ := hy
    obtain ⟨k, hk, hs⟩ := hi.size
    have hv := hi.val hP
    rcases U.free q k hk with e | e <;> omega
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  -- a childless cap after: childless before, or the deleted cap's parent
  have hnc' : (¬ ∃ x, σ'.cdt x = some u) → (¬ ∃ x, σ.cdt x = some u) ∨
      (σ.cdt sl = some u ∧ (∀ x, σ.cdt x = some u → x = sl) ∧ ∀ x, σ.cdt x ≠ some sl) := by
    intro h0
    by_cases hb : ∃ x, σ.cdt x = some u
    · right
      obtain ⟨x0, hx0⟩ := hb
      have hall : ∀ x, σ.cdt x = some u → x = sl := by
        intro x hx
        by_contra hxs
        apply h0
        refine ⟨x, ?_⟩
        rw [hcdt, Function.update_of_ne hxs]
        have : σ.cdt x ≠ some sl := by rw [hx]; exact fun e => hune (Option.some.inj e)
        show (if σ.cdt x = some sl then σ.cdt sl else σ.cdt x) = some u
        rw [if_neg this, hx]
      have hsl : σ.cdt sl = some u := by have := hall x0 hx0; rw [← this]; exact hx0
      refine ⟨hsl, hall, fun x hx => h0 ⟨x, ?_⟩⟩
      have hxs : x ≠ sl := fun e => by rw [e, hsl] at hx; exact hune (Option.some.inj hx)
      rw [hcdt, Function.update_of_ne hxs]
      show (if σ.cdt x = some sl then σ.cdt sl else σ.cdt x) = some u
      rw [if_pos hx, hsl]
    · exact Or.inl hb
  have hmem : ∀ y ∈ G'.chains.flatten, y ∈ Z.G.chains.flatten := by
    intro y hy
    obtain ⟨hys, c0, h0', hn⟩ := (hM'.members y).1 hy
    have e : y ≠ cslotAddr sl := fun e => by rw [e, capAt_capV, hnull] at h0'; exact hn (eq_of_ok_eq h0').symm
    have hc0 : capAt (L.mem s) y = ok c0 := by rw [capAt_capV, ← hcap y hys e, ← capAt_capV]; exact h0'
    exact (hM.members y).2 ⟨hys, c0, hc0, hn⟩
  refine ⟨U.pal, U.pfit, U.fiLe, U.high, by rw [hcpu, hna]; exact U.actZ, U.free, fun w hal h1 h2 => ?_, U.sb4,
    U.nostr, fun y hy => U.nsFree y (hmem y hy), fun h0 y hy => ?_, fun k0 v0 => by simpa only [hna] using U.pp k0 v0,
    fun h0 hf0 => ?_, by rw [hna]; exact U.dwReg, by rw [hgp]; exact U.gReg⟩
  · rw [hw.mem_eq hal fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega]
    exact U.zero w hal h1 h2
  · rcases hnc' h0 with hnc | ⟨g1, g2, g3⟩
    · exact U.ns hnc y (hmem y hy)
    · obtain ⟨hys, c0, h0', hn⟩ := (hM'.members y).1 hy
      exact (hUt u p sb fi dev hu hcap0 g1 g2 g3).1 y hys (by rw [show capV (L.mem s') y = c0 from capV_of_capAt h0']; exact hn)
  · rcases hnc' h0 with hnc | ⟨g1, g2, g3⟩
    · obtain ⟨r1, r2, r3⟩ := U.rst hnc hf0
      exact ⟨fun sl' h => r1 sl' (horig sl' h), r2, by rw [hna, hDbg]; exact r3⟩
    · exact (hUt u p sb fi dev hu hcap0 g1 g2 g3).2 hf0

theorem KBack.trans' {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : KBack σ1 σ2) (h2 : KBack σ2 σ3) : KBack σ1 σ3 := by
  intro o ko3 h3
  obtain ⟨ko2, h2', a1, a2, a3, a4, a5, a6⟩ := h2 o ko3 h3
  obtain ⟨ko1, h1', b1, b2, b3, b4, b5, b6⟩ := h1 o ko2 h2'
  exact ⟨ko1, h1', b1 ∘ a1, b2 ∘ a2, b3 ∘ a3, b4 ∘ a4, b5 ∘ a5, b6 ∘ a6⟩

/-- The current SC is an SC of `H` (`CurOwnW`: the owner's SC, `Inv.back`,
or an SC of the sets; `JPlaced`). -/
theorem JAtZ.csc_sc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : ∃ z, H (L.cscW s) = some (.sc z) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have ecs : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA nodeW; rw [hc.cur]
  have hcv0 : σ.curSc = (L.cscW s).bv := by rw [ecs]; exact hs.curSc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkx : ∃ x n, σ.kheap σ.curSc = some (.schedContext x n) := by
    rcases J.own with ⟨u, -, xt, hkt, hxs, -, -⟩ | ⟨⟨c, hcC, hcv⟩, -⟩
    · obtain ⟨y, n, hy, -⟩ := J.inv.back _ xt _ hkt hxs; exact ⟨y, n, hy⟩
    · obtain ⟨x, n, hk, -⟩ := hs.scs c hcC; exact ⟨x, n, by rw [← hcv]; exact hk⟩
  obtain ⟨x, n, hx⟩ := hkx
  rw [hcv0] at hx
  have h0 : L.cscW s ≠ 0#u64 := fun e => by
    have := J.kern.cscH; rw [e, J.kern.h0] at this; exact this rfl
  exact ⟨_, (hJ.sc _ x n h0 hx).2⟩

set_option maxHeartbeats 16000000 in
/-- **Emptying a notification cap's CNode slot keeps `JAtZ`** (module
docstring): the dead set grows by the objects no longer covered, at most the
notification, then dead (`hpd`: dead before, or another cap to it covers
it); the untyped caps' facts by `del_utc`, `DelUtFact` given after. -/
theorem JAtZ.emptyNtfnJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl)
    (hcnode : ∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length))
    {p b : U64} {w r : Bool} (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r))
    (hpd : DeadP (L := L) H s p ∨
      ∃ y ∈ Z.G.chains.flatten, y ≠ cslotAddr sl ∧ ∃ b' w' r', capV (L.mem s) y = .Notification p b' w' r') :
    cdt.empty_slot st arI s a (cslotAddr sl) .Null ⦃ res => res.2 = a ∧ ∃ σ' G' V',
      ((), σ') ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ).1 ∧ XTopAt (L := L) AR (Z.mv G' V') res.1 res.2 σ' ∧
      L.ksb res.1 = L.ksb s ∧ KBack σ σ' ∧
      ((∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelUtFact (L := L) Z.th res.1 σ' up usb ufi) →
       JCs (L := L) (Z.mv G' V') res.1 σ' ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' res.1 σ') ⦄ := by
  have hP := J.xtop.rel.1
  have hR := J.xtop.rel.2.1.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  let W : S → A → Fl4Spec.State Unit → MdbGhost → Prop := fun s2 a2 σ2 G2 =>
    WXZ (L := L) AR Z (L.ksb s) s2 a2 σ2 G2 ∧ P1.WritesIn st s s2 (Sched.SlotWd Z.th) ∧ Ipc.CnK σ σ2 ∧ a2 = a
  have hSl : SlotHypW (L := L) (A := A) W Z.th := fun s1 s2 a1 σ1 σ2 G1 G2 hW hD1 hD2 hF hcn hSt =>
    ⟨slotHypW_XZ AR Z (L.ksb s) s1 s2 a1 σ1 σ2 G1 G2 hW.1 hD1 hD2 hF hcn hSt, hW.2.1.trans1 (SlotFrame2.writesIn hF),
      hW.2.2.1.trans hcn, hW.2.2.2⟩
  have hW0 : W s a σ Z.G := ⟨⟨⟨Z.vs, J.xtop⟩, J.ks, J.thT, rfl⟩, P1.WritesIn.refl _ _, Ipc.CnK.refl σ, rfl⟩
  refine WP.spec_mono (empty_stepW' arI W Z.th hP (cl := .Null) (fun h => absurd rfl h) hSl s a σ Z.G hDS hW0 hA
    trivial trivial) ?_
  rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hnull2, hoth2, -, -, -, -, ⟨⟨V2, hX2⟩, -, -, -⟩, hwS, hcn2, ha2⟩
  simp only at hes hDS2 hnull2 hoth2 hX2 hwS hcn2 ha2 ⊢
  subst ha2
  have hw : P1.WritesIn st s s2 (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  -- the slot's CNode; the spec state after
  obtain ⟨q, hq1, hq2⟩ := hcnode
  obtain ⟨cs, hkq, hwf, -⟩ := hR.cnode q _ hq2
  obtain ⟨o, idx⟩ := sl
  simp only at hq1 hq2 hkq
  subst hq1
  change ((), σ2) ∈ (Fl4Spec.emptySlot (Z := Unit) (q.bv, idx) .nullCap σ).1 at hes
  have hkc : KeepC σ σ2 := keepC_of hcn2 (emptySlot_null_nko _ σ ((), σ2) hes)
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact ⟨_, cs, hkq⟩)
  have hkz : KSz σ σ2 := emptySlot_null_nkz _ σ ((), σ2) hes
  obtain ⟨c0, ac, hc0, hca, hg⟩ := hR.abs_cap hA
  rw [hc] at hc0
  obtain rfl : (capability.Cap.Notification p b w r) = c0 := eq_of_ok_eq hc0
  rw [hca.abs] at hg
  have h3 : Fl4Spec.setCap (Z := Unit) .nullCap (q.bv, idx) (emptySlotCdtState σ (q.bv, idx)) =
      ({((), setCnodeSlot (emptySlotCdtState σ (q.bv, idx)) q.bv idx.length cs idx .nullCap)}, False) :=
    setCap_cnode (σ := emptySlotCdtState σ (q.bv, idx)) .nullCap hkq hwf rfl
  have he := emptySlot_eq hg (by simp [absCap]) h3
  rw [he] at hes
  have e2 := mem_singleton_snd hes
  simp only at e2
  subst e2
  have hcdt := (rfl : (setCnodeSlot (emptySlotCdtState σ (q.bv, idx)) q.bv idx.length cs idx .nullCap).cdt = _)
  -- the frames
  have hgp : (setCnodeSlot (emptySlotCdtState σ (q.bv, idx)) q.bv idx.length cs idx .nullCap).archState.x64GlobalPml4 =
      σ.archState.x64GlobalPml4 := rfl
  obtain ⟨⟨hR2, hV2, hM2, hC2, hI2⟩, hDl2, hFI2⟩ := hDS2
  have hMO := hX2.rel.2.2.2.2.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ntfn := (hJ.typed _ hA.isSlot).2.1 p b w r (capV_of_capAt hc) |>.2
  have hpfit : p.val + 2 ^ 6 ≤ 2 ^ 64 := J.kern.heap.fits p _ hHp
  have hTK : TypedKept Z.th (L.mem s) (L.mem s2) := fun x hx => by
    by_cases e : x = cslotAddr (q.bv, idx)
    · left; rw [e, hnull2]; rfl
    · right; exact ⟨x, hx, by rw [hoth2 x hx e]⟩
  have hT3 : ∀ t, Z.th t = some .tcb → capAt (L.mem s2) (slotOf t 3) = capAt (L.mem s) (slotOf t 3) := by
    intro t ht
    have h1 : IsSlot Z.th (slotOf t 3) := ⟨t, 3, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hne : slotOf t 3 ≠ cslotAddr (q.bv, idx) := by
      intro e
      obtain ⟨p', i, hi, hp1, hp2⟩ := AbsSlot.at (th := Z.th) (sl := (q.bv, idx)) hA
      have hpp : p' = q := P1.eq_of_bv hp1.symm
      subst hpp
      have := IsSlotAt.apart hP (Or.inr ⟨ht, by decide⟩ : IsSlotAt Z.th t 3) hi (fun hh => by
        obtain ⟨h, -⟩ := hh; subst h; rw [hq2] at ht; cases ht)
      rw [e, hp2] at this; omega
    rw [capAt_capV, capAt_capV, hoth2 _ h1 hne]
  have hUK : UtKept Z.th (L.mem s) (L.mem s2) := fun x hx p' sb fi d h => by
    have e : x ≠ cslotAddr (q.bv, idx) := fun e => by rw [e, hnull2] at h; cases h
    exact ⟨x, hx, fi, d, by rw [← hoth2 x hx e]; exact h, Or.inl le_rfl⟩
  -- the cover after
  have hmemA : ∀ y, IsSlot Z.th y → capV (L.mem s2) y ≠ .Null → y ∈ G2.chains.flatten := fun y hy hn =>
    (hM2.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
  have hcovA : ∀ lo hi, Covered (L.mem s) Z.G lo hi → Covered (L.mem s2) G2 lo hi ∨
      (p.val ≤ lo ∧ hi ≤ p.val + 2 ^ 6 ∧ DeadP (L := L) H s p) := by
    rintro lo hi ⟨y, hy, hp1, hu1, hb1, ht1⟩
    obtain ⟨hys, -⟩ := (J.xtop.rel.2.1.2.2.1.members y).1 hy
    by_cases e : y = cslotAddr (q.bv, idx)
    · subst e
      rw [capV_of_capAt hc] at hb1 ht1
      obtain ⟨e1, e2⟩ := range_ntfn p b w r hpfit
      rcases hpd with hd | ⟨y', hy', hne', b', w', r', hy'c⟩
      · rw [e1] at hb1; rw [e2] at ht1
        exact Or.inr ⟨hb1, by omega, hd⟩
      · obtain ⟨hy's, -⟩ := (J.xtop.rel.2.1.2.2.1.members y').1 hy'
        have hc' : capV (L.mem s2) y' = .Notification p b' w' r' := by rw [hoth2 y' hy's hne']; exact hy'c
        obtain ⟨f1, f2⟩ := range_ntfn p b' w' r' hpfit
        refine Or.inl ⟨y', hmemA y' hy's (by rw [hc']; nofun), by rw [hc']; exact ok_inj (phys_eq _).symm, by rw [hc']; rfl,
          by rw [hc', f1]; rw [e1] at hb1; exact hb1, by rw [hc', f2]; rw [e2] at ht1; exact ht1⟩
    · have hcs := hoth2 y hys e
      have hnn : capV (L.mem s) y ≠ .Null := fun h => by rw [h, physF_null] at hp1; cases hp1
      exact Or.inl ⟨y, hmemA y hys (by rw [hcs]; exact hnn), by rw [hcs]; exact hp1, by rw [hcs]; exact hu1,
        by rw [hcs]; exact hb1, by rw [hcs]; exact ht1⟩
  have hHth : ∀ q' k, Z.th q' = some k → ∃ k', H q' = some k' ∧ 2 ^ k'.bits ≤ max (objSize k) 1 := by
    intro q' k hk
    rcases J.thk q' k hk with rfl | ⟨r', rfl⟩
    · exact ⟨.tcb, (hJ.tcb q').1 hk, by simp [objSize, P1.HKind.bits]⟩
    · refine ⟨.other (r' + 5), hJ.cnode q' r' hk, ?_⟩
      simp only [objSize, P1.HKind.bits]
      rw [pow_add]; omega
  -- an object of `H` in the notification's range is the notification
  have hin : ∀ q' k', H q' = some k' → p.val ≤ q'.val → q'.val + 2 ^ k'.bits ≤ p.val + 2 ^ 6 → q' = p := by
    intro q' k' hk' h1 h2
    by_contra hne
    have := J.kern.heap.disj q' k' p .ntfn hk' hHp hne
    rw [show (P1.HKind.ntfn).bits = 6 from rfl] at this
    have : 1 ≤ 2 ^ k'.bits := Nat.one_le_two_pow
    omega
  have hunc : ∀ q', q' ∈ Uncov Z.th H (L.mem s2) G2 → DeadP (L := L) H s2 q' := by
    intro q' hq'
    by_cases hD : q' ∈ D
    · exact J.deadP_slot hX2 hcn2 (KeepC.t hkc) hw (J.jcov.dead q' hD)
    rcases hq' with ⟨k, hk, hnc⟩ | ⟨k, hk, hnc⟩
    · rcases J.jcov.th q' k hk with hcv | hD'
      · rcases hcovA _ _ hcv with h | ⟨g1, g2, hd⟩
        · exact absurd h hnc
        · exfalso
          obtain ⟨k', hk', hle⟩ := hHth q' k hk
          have e := hin q' k' hk' g1 (by omega)
          subst e
          rw [hHp] at hk'; cases hk'
          rcases J.thk q' k hk with rfl | ⟨r', rfl⟩
          · rw [(hJ.tcb q').1 hk] at hHp; cases hHp
          · rw [hJ.cnode q' r' hk] at hHp; cases hHp
      · exact absurd hD' hD
    · rcases J.jcov.h q' k hk with hcv | hD'
      · rcases hcovA _ _ hcv with h | ⟨g1, g2, hd⟩
        · exact absurd h hnc
        · have e := hin q' k hk g1 g2
          subst e
          exact J.deadP_slot hX2 hcn2 (KeepC.t hkc) hw hd
      · exact absurd hD' hD
  have hks2 : ∀ x ∈ G2.chains.flatten, ∀ p' sb fi d, capV (L.mem s2) x = .Untyped p' sb fi d →
      (p'.val + 2 ^ sb.val ≤ (L.ksb s2).val ∨ (L.ksb s2).val + 13568 ≤ p'.val) ∧
      ∀ c ∈ Cs, p'.val + 2 ^ sb.val ≤ L.nodeBase s2 c ∨ L.nodeBase s2 c + 4288 ≤ p'.val := by
    intro x hx p' sb fi d hcx
    obtain ⟨hxs, c1, hc1, hn1⟩ := (hM2.members x).1 hx
    have e : x ≠ cslotAddr (q.bv, idx) := fun e => by rw [e, hnull2] at hcx; cases hcx
    have hcx0 : capV (L.mem s) x = .Untyped p' sb fi d := by rw [← hoth2 x hxs e]; exact hcx
    have hxm : x ∈ Z.G.chains.flatten :=
      (J.xtop.rel.2.1.2.2.1.members x).2 ⟨hxs, _, capAt_capV _ _, by rw [hcx0]; nofun⟩
    obtain ⟨k1, k2⟩ := J.jcov.ks x hxm p' sb fi d hcx0
    have hks : L.ksb s2 = L.ksb s := hw.1
    have hnb : ∀ c, L.nodeBase s2 c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
    exact ⟨by rw [hks]; exact k1, fun c hc => by rw [hnb]; exact k2 c hc⟩
  have hjc := J.jcov.step hunc (fun q' _ hd => J.deadP_slot hX2 hcn2 (KeepC.t hkc) hw hd) hks2
  have hcl : L.cscW s ∉ D ∪ Uncov Z.th H (L.mem s2) G2 := by
    obtain ⟨z, hz⟩ := J.csc_sc
    rintro (h | h)
    · exact J.kern.cscLive h
    · have hcp : L.cscW s ≠ p := fun e => by rw [e, hHp] at hz; cases hz
      rcases h with ⟨k, hk, hnc⟩ | ⟨k, hk, hnc⟩
      · rcases J.thk _ k hk with rfl | ⟨r', rfl⟩
        · rw [(hJ.tcb _).1 hk] at hz; cases hz
        · rw [hJ.cnode _ r' hk] at hz; cases hz
      · rw [hz] at hk; cases hk
        rcases J.jcov.h _ _ hz with hcv | hD'
        · rcases hcovA _ _ hcv with h | ⟨g1, g2, -⟩
          · exact hnc h
          · exact hcp (hin _ _ hz g1 g2)
        · exact J.kern.cscLive hD'
  have horig : ∀ sl', (setCnodeSlot (emptySlotCdtState σ (q.bv, idx)) q.bv idx.length cs idx .nullCap).isOriginalCap sl' = true →
      σ.isOriginalCap sl' = true := fun sl' h => by
    by_cases e : sl' = (q.bv, idx)
    · subst e; simp [setCnodeSlot, emptySlotCdtState] at h
    · simpa [setCnodeSlot, emptySlotCdtState, Function.update_of_ne e] using h
  refine ⟨rfl, _, G2, V2, by rw [he]; exact Set.mem_singleton _, hX2, hw.1, KBack.of_keepC hkc, fun hUt => ?_⟩
  have hutc := J.del_utc (G' := G2) (sl := (q.bv, idx)) (fun y hy e => hoth2 y hy e) hnull2 hw rfl horig hgp hM2 hUt
  obtain ⟨hJC, R⟩ := jowes_slotD J hX2 hcn2 (KeepC.t hkc) hw hFI2 hMO hkz hTK (fun t ht => Or.inl (hT3 t ht)) hDl2 hUK hjc hcl
    (fun sl' h => Or.inl (horig sl' h)) hutc
  exact ⟨hJC, Ac, Lst, _, R⟩

/-- **The untyped caps a notification cap's deletion leaves childless** [J]
(`DelUtFact`, at the state after; module docstring). -/
def DelUtHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool),
    AbsSlot th sl → capV (L.mem s) (cslotAddr sl) = .Notification p b w r →
    cdt.delete_one st arI s a (cslotAddr sl) = ok (s', a') → ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
      ∀ u up usb ufi udev, AbsSlot th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelUtFact (L := L) th s' σ' up usb ufi

/-- A non-final notification cap has another cap to its notification in the
MDB (`final_iff`, `FinM.key`: overlapping caps, no zombie, share their
object key). -/
theorem other_ntfn {th : TypedHeap} (hP : Placed th) {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) {p b : U64} {w r : Bool}
    (hcv : capV (L.mem s) (cslotAddr sl) = .Notification p b w r)
    (hfin : ¬ Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ) :
    ∃ y ∈ G.chains.flatten, y ≠ cslotAddr sl ∧ ∃ b' w' r', capV (L.mem s) y = .Notification p b' w' r' := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hF⟩ := hDS
  have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
  have hne : Fl4Spec.genObjRefs (absCap (capV (L.mem s) (cslotAddr sl))) ≠ ∅ := by
    rw [hcv]; exact needsFin_refs hNF
  rw [← hcv] at hfin
  have hx : cslotAddr sl ∈ G.chains.flatten := (hM.members _).2 ⟨hA.isSlot, _, capAt_capV _ _, by rw [hcv]; nofun⟩
  by_contra hno
  apply hfin
  refine (final_iff hP hR hM hF hA hne).2 fun y hy hyx hov => hno ⟨y, hy, hyx, ?_⟩
  have hzy : isZb (capV (L.mem s) y) = false := by
    cases h : isZb (capV (L.mem s) y)
    · rfl
    · exact absurd hov.symm (hF.fm.zfin y hy _ hx hyx h)
  have hk := hF.fm.key _ hx y hy (Ne.symm hyx) hov (by rw [hcv]; rfl) hzy (by rw [hcv]; simp [isFrame])
  rw [hcv] at hk
  cases h : capV (L.mem s) y <;> rw [h] at hk <;> simp [okey] at hk
  subst hk
  exact ⟨_, _, _, rfl⟩

/-- A non-final object cap but a frame has another cap alike it (the same
object key) in the MDB (as `other_ntfn`). -/
theorem other_key {th : TypedHeap} (hP : Placed th) {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) {c : capability.Cap}
    (hcv : capV (L.mem s) (cslotAddr sl) = c) (hk : FinObjKind c) (hf : isFrame c = false)
    (hfin : ¬ Fl4Spec.isFinalCap' (absCap c) σ) :
    ∃ y ∈ G.chains.flatten, y ≠ cslotAddr sl ∧ okey (capV (L.mem s) y) = okey c := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hF⟩ := hDS
  have hNF : NeedsFin c := Or.inl ⟨hk, hf⟩
  have hne : Fl4Spec.genObjRefs (absCap (capV (L.mem s) (cslotAddr sl))) ≠ ∅ := by
    rw [hcv]; exact needsFin_refs hNF
  rw [← hcv] at hfin
  have hx : cslotAddr sl ∈ G.chains.flatten :=
    (hM.members _).2 ⟨hA.isSlot, _, capAt_capV _ _, by rw [hcv]; rintro rfl; exact hk⟩
  have hzx : isZb (capV (L.mem s) (cslotAddr sl)) = false := by
    rw [hcv]; cases c <;> simp only [FinObjKind] at hk <;> rfl
  by_contra hno
  apply hfin
  refine (final_iff hP hR hM hF hA hne).2 fun y hy hyx hov => hno ⟨y, hy, hyx, ?_⟩
  have hzy : isZb (capV (L.mem s) y) = false := by
    cases h : isZb (capV (L.mem s) y)
    · rfl
    · exact absurd hov.symm (hF.fm.zfin y hy _ hx hyx h)
  rw [← hcv]
  exact (hF.fm.key _ hx y hy (Ne.symm hyx) hov hzx hzy (by rw [hcv, hf]; simp)).symm

set_option maxHeartbeats 16000000 in
/-- **`JStepHyps.del` from `DelUtHyp`** (module docstring): the finalisation
(`finNtfnJ` when final, nothing otherwise), then the slot emptied
(`emptyNtfnJ`; the notification dead after a final cap's finalisation,
P1's `fin_cap_ntfn.dead`, or covered by another cap, `other_ntfn`). -/
theorem jowes_del [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hUt : DelUtHyp (L := L) (arI := arI) AR th) :
    ∀ (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool),
      AbsSlot th sl → (∃ q, sl.1 = q.bv ∧ th q = some (.cnode sl.2.length)) →
      capV (L.mem s) (cslotAddr sl) = .Notification p b w r →
      cdt.delete_one st arI s a (cslotAddr sl) = ok (s', a') → ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 →
      ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → ∃ (G' : MdbGhost) (V' : XVs),
          XTopAt (L := L) AR (Z.mv G' V') s' a' σ' ∧ L.ksb s' = L.ksb s ∧ KBack σ σ' ∧
          JCs (L := L) (Z.mv G' V') s' σ' ∧
          ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
            JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ' := by
  intro s s' a a' σ σ' sl p b w r hA hcnode hcv0 hrun hm Z H Cs Ac Lst D hth J
  have hU0 := hUt s s' a a' σ σ' sl p b w r hA hcv0 hrun hm Z H Cs Ac Lst D hth J
  subst hth
  have hP := J.xtop.rel.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  obtain ⟨c, ac, hc0, hca, hg⟩ := hDS.1.1.abs_cap hA
  rw [hca.abs] at hg
  have hcv := capV_of_capAt hc0
  rw [hcv] at hcv0; subst hcv0
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ntfn := ((hJ.typed _ hA.isSlot).2.1 p b w r hcv).2
  have hpN : p ∈ Z.N := J.hset.2.1 p hHp
  have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
  -- the spec's deletion from the finalisation's and the emptying's outcomes
  have hspec : ∀ (σ1 σ2 : Fl4Spec.State Unit) (cl : capability.Cap),
      ((absCap .Null, absCap cl), σ1) ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Notification p b w r))
        (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) σ).1 →
      ((), σ2) ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ1).1 →
      ((), σ2) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 := by
    intro σ1 σ2 cl hmem hes
    unfold Fl4Spec.capDeleteOne
    refine mem_bind_nd (x := (absCap (.Notification p b w r), σ)) (by rw [hg]; rfl) ?_
    simp only [absCap, Fl4Spec.NonDet.unless, reduceCtorEq, ↓reduceIte]
    refine mem_bind_nd (x := (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ), σ)) rfl ?_
    refine mem_bind_nd (x := ((), σ1)) (fastFinalise_of_finaliseCap hmem) ?_
    exact hes
  have key : cdt.delete_one st arI s a (cslotAddr sl) ⦃ res => ∃ σ2 G2 V2,
      ((), σ2) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 ∧ XTopAt (L := L) AR (Z.mv G2 V2) res.1 res.2 σ2 ∧
      L.ksb res.1 = L.ksb s ∧ KBack σ σ2 ∧
      ((∀ u up usb ufi udev, AbsSlot Z.th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelUtFact (L := L) Z.th res.1 σ2 up usb ufi) →
       JCs (L := L) (Z.mv G2 V2) res.1 σ2 ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JRest (L := L) arI (Z.mv G2 V2) H Cs Ac' Lst' D' res.1 σ2) ⦄ := by
    unfold cdt.delete_one
    rw [slot_cap_eq, hc0]
    simp only [bind_ok, cap_is_null_eq]
    simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨bf, hbf, hbf2, -⟩ := finalHyp_full Z.th hP s σ Z.G sl _ hDS hA hc0 hcn
    have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
    rw [hbf2 hNF] at hbf
    rw [is_final_with_cap_eq _ _ _ hc0, hbf]; simp only [bind_ok]
    rw [← finalise_cap_ntfn arI s a p b w r _ false]
    by_cases hfin : Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ
    · have hdt : decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ) = true := decide_eq_true hfin
      rw [hdt]
      refine WP.spec_bind (WP.spec_and (J.finNtfnJ hpN) (P1.fin_cap_ntfn.dead (ar := arI) s a p b w r false J.blk hHp hHp)) ?_
      rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, e2, σ1, V1, hmem1, J1, hkb1, hSS1, hks1⟩, d1, d2, d3⟩
      simp only at e1 e2 hmem1 J1 hkb1 hSS1 hks1 d1 d2 d3
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
      subst e2
      simp only [uncurry_apply_pair]
      have hdp : DeadP (L := L) H s1 p :=
        ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ => ⟨d1, d2, d3⟩,
          fun h => (by rw [hHp] at h; cases h), fun z h => (by rw [hHp] at h; cases h)⟩
      have hc1 : capAt (L.mem s1) (cslotAddr sl) = ok (.Notification p b w r) := by
        rw [capAt_capV, hSS1.capV hA.isSlot, hcv]
      have hcdt1 : σ1.cdt = σ.cdt := (finNtfn_nkc p.bv b.bv _ true σ _ hmem1).cdt
      refine WP.spec_mono (J1.emptyNtfnJ hA hcnode hc1 (Or.inl hdp)) ?_
      rintro ⟨s2, a2⟩ ⟨e3, σ2, G2, V2, hes, hX2, hks2, hkb2, hR2⟩
      simp only at e3 hes hX2 hks2 hkb2 hR2 ⊢
      subst e3
      refine ⟨σ2, G2, V2, hspec σ1 σ2 .Null (by rw [hdt]; exact hmem1) hes, hX2, hks2.trans hks1,
        hkb1.trans' hkb2, fun hU => hR2 fun u up usb ufi udev hu hcu h1 h2 h3 => ?_⟩
      rw [hcdt1] at h1 h2 h3
      exact hU u up usb ufi udev hu (by rw [capAt_capV, ← hSS1.capV hu.isSlot, ← capAt_capV]; exact hcu) h1 h2 h3
    · have hdf : decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ) = false := decide_eq_false hfin
      rw [hdf]
      obtain ⟨cl, he, hmem, hcl, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ (.Notification p b w r) trivial
        false (fun hw => by have := finWork_ntfn hw; cases this)
      have hcl0 : cl = .Null := hnio (fun f l e => by cases e)
      subst hcl0
      rw [he]; simp only [bind_ok]
      simp only [uncurry_apply_pair]
      refine WP.spec_mono (J.emptyNtfnJ hA hcnode hc0 (Or.inr (other_ntfn hP hDS hA hcv hfin))) ?_
      rintro ⟨s2, a2⟩ ⟨e3, σ2, G2, V2, hes, hX2, hks2, hkb2, hR2⟩
      simp only at e3 hes hX2 hks2 hkb2 hR2 ⊢
      subst e3
      exact ⟨σ2, G2, V2, hspec σ σ2 .Null (by rw [hdf]; exact hmem) hes, hX2, hks2, hkb2, hR2⟩
  rw [hrun, WP.spec_ok] at key
  obtain ⟨σ2, G2, V2, hm2, hX2, hks2, hkb2, hR2⟩ := key
  have e := (Det.detAt_capDeleteOne_ntfn hg).eq hm2 hm
  have e2 : σ2 = σ' := congrArg Prod.snd e
  subst e2
  obtain ⟨hC2, R2⟩ := hR2 hU0
  exact ⟨G2, V2, hX2, hks2, hkb2, hC2, R2⟩

/-- **`JStepHyps` from the untyped caps' deletion facts alone**
(`JStepHyps.of_del` with `jowes_del`): the only named premise left of the
primitive steps' closure is `DelUtHyp` [J]. -/
theorem JStepHyps.of_ut [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hUt : DelUtHyp (L := L) (arI := arI) AR th) :
    JStepHyps (L := L) arI AR th :=
  JStepHyps.of_del arI (jowes_del hUt)

end

end

end Fl4Proofs.P3
