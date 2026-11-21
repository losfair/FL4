/-
P3 (DESIGN.md §9), VSpace: **the native VSpace caps' decodes from `JAtZ`**
(XTopJointEntry's `JPath`): VsThX's producers at `FinXR` (the spec's decode
and invocation refined, every label), their premises from `JAtZ` at the
entry. The map, unmap, flush and ASID assignment steps are proved at `J`
in XTopJointVsMap (`decode_invocation_{page_table, page_directory, pdpt,
pml4, asid_pool, frame}JV`, no per-op premise), `MakePool` in
XTopJointMakePool; here the shared pieces and the paths' premises.

* `JAtZ.ctTcb`: the current thread a TCB of the typed heap (`CurOK`).
* `JVsExtra`: the front end's first extra cap (VSpace's `vspace.extra`; from
  `ExtraOK`, `ExtraOK.vsExtra`).
* `XCap.jatR`: `XCap` at `FinXR` with `JPostHyp` at `JAt` (the frame cap's
  `DeriveSubframe` label, XTopJointVsMap's `decode_invocation_frameJV`).
* `MakePool`'s split: `MpClean` (no dead object and no IPC-buffer word in a
  childless pool-sized untyped's region) and `MpSpecClean` (no spec object
  there); clean, `MpPlacedHyp` and the region facts are proved
  (`JAtZ.mpEmpty`, `JAtZ.mpOObj`, `JAtZ.mpPlacedC`, `JAtZ.mpRegionC`; they
  were [J] premises, false in reachable states with a dead object there) and
  the cap is proved at `J` in XTopJointMakePool
  (`decode_invocation_asid_controlJM`); dirty, the cap at `J` [W] (the
  detype).
* `ExtraOK.vsExtra`, `.poolExtra`, `.mpExtra`: the extra caps from the front
  end's `ExtraOK` (they were [W] path fields).
* `J{Pool,Frame,AsidC}Path`: each cap's premises left, as XTopJointEntry's
  `JPath` names them: the frame's `hno` [J] (l4v `valid_cap`/`cap_range`
  disjointness), the pool's extra cap native ([scope]: guest-root
  assignment, DESIGN §9), MakePool's dirty case [W]. The labels are proved
  (FrontEndLabel), the page table/directory/PDPT/PML4 paths ask nothing. No
  `JPostHyp` is left (the frame's `DeriveSubframe` at `J` in XTopJointVsSub,
  `MakePool` in XTopJointMakePool).
-/
import Fl4Proofs.P3.VsThX
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.FrontEndExtra
import Fl4Proofs.P3.UtDropJ2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The current thread of a `JAtZ` state is a TCB of the typed heap
(`CurOK`). -/
theorem JAtZ.ctTcb {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) : σ.curThread = ct.bv ∧ Z.th ct = some .tcb := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨t, ht, hth, -⟩ := J.xtop.fin.2.2.2.2
  have e : t = ct := P1.eq_of_bv (ht.trans hcur)
  subst e
  exact ⟨hcur, hth⟩

/-- **The front end's first extra cap of a VSpace decode** (proved from
`ExtraOK`: `ExtraOK.vsExtra`). -/
structure JVsExtra (Z : XSets) (s : S) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop where
  hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
    ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
      CapRel vc vc' ∧ excaps = (vc', xsl) :: rest
  hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot Z.th x

/-- `XCap` at `FinXR` and `JPostHyp` give it at `JAt` (`XCap.jat`). -/
theorem XCap.jatR {Z' : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64}
    {c : capability.Cap} {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCap (L := L) arI (FinXR (L := L) AR Z') s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl
      excaps buffer ct) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps
      buffer ct :=
  XCap.jat arI (h.imp arI fun _ _ _ hx => xtop_of_finXR hx) J hR

/-- **The front end's extra caps of `MakePool`** (proved from `ExtraOK`:
`ExtraOK.mpExtra`; the untyped cap's
slot a CNode slot of the typed heap, the root cap's valid and held in a
slot of the typed heap: the front end's extra caps are looked up from the
caller's CSpace, as `JVsExtra.hxs`). The region facts the decode needs of a
childless untyped (`MpRegion`, `RegOKTop`) are proved from `JAtZ` when the
regions are clean (`JAtZ.mpRegionC`). -/
def JMpExtra (Z : XSets) (s : S)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop :=
  (∀ y, vspace.extra extra 1#usize = ok (some y) → IsSlot Z.th y) ∧
  ((∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
      (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
    ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
      (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
      (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
      Z.th pp = some (.cnode rs) ∧ idx.length = rs ∧
      vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
      capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
      capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid Z.th rc ∧
      excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest)

/-- **MakePool's regions are clean** (the split of the ASID control path):
for every childless pool-sized RAM untyped cap of the MDB, no dead object
(of `th` or `H`) meets its region `[p, p + 4096)`, and no IPC-buffer word
(FL4's word, the spec's bytes) lies there. Then the region holds no object
at all (`JAtZ.mpEmpty`: covered objects miss it by `ut_free`, the idle and
kernel-state objects by `JCovD`), l4v's `delete_objects` removes nothing,
and MakePool's placement facts hold (`JAtZ.mpPlacedC`, `JAtZ.mpRegionC`).

Not a premise: a state where it fails is reachable (retype a TCB, a CNode
or an endpoint from a 4 KiB untyped, delete its last cap: the object is
dead, `JCovD`, and stays in `th`/`H`, the sets and the spec heap until a
retype or MakePool detypes the region). `MpPlacedHyp` and the region facts
of the old `JMpExtra` were false there (a dead TCB of `th` in the region is
not a TCB of `restrictTh th p (p + 4096)`; a dead CNode of `th` breaks
`MpRegion.ncn`), so the ASID control path asks the dirty case separately
(`JAsidCPath.dirty` [W]). -/
def MpClean (Z : XSets) (H : P1.Heap) (D : Set U64) (s : S) : Prop :=
  ∀ x ∈ Z.G.chains.flatten, ∀ p fi, capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
    (∀ y, ¬ Mdb.Desc Z.G.par y x) →
    (∀ q ∈ D, (∀ k, Z.th q = some k → q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 4096 ≤ q.val) ∧
      (∀ k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val)) ∧
    ∀ wp ∈ Z.B, (wp.1.val + 8 ≤ p.val ∨ p.val + 4096 ≤ wp.1.val) ∧
      ∀ i ∈ Fl4Spec.intUpto 0 7, (wp.2 + (7 - BitVec.ofInt 64 i)).toNat < p.val ∨
        p.val + 4096 ≤ (wp.2 + (7 - BitVec.ofInt 64 i)).toNat

/-- **No spec object in MakePool's regions** (the second half of the clean
case): for every childless pool-sized RAM untyped cap of the MDB, the spec
has no object at an address in its region `[p, p + 4096)`. Every live spec
object is one of `th`'s or `H`'s (`KTyped`, `SpecCover`, `ObjCover`) and
`MpClean` keeps those out of the region, so only a dead object (a CNode the
typed heap lost track of) can sit there; l4v's `delete_objects` removes it
(the detype, `JAsidCPath.dirty`). Not a premise: a case split. -/
def MpSpecClean (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ Z.G.chains.flatten, ∀ p fi, capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
    (∀ y, ¬ Mdb.Desc Z.G.par y x) → ∀ o ko, σ.kheap o = some ko → o.toNat < p.val ∨ p.val + 4096 ≤ o.toNat

theorem two_pow_asidPool : 2 ^ (fl4_abi.consts.bits.ASID_POOL).val = 4096 := by
  unfold fl4_abi.consts.bits.ASID_POOL; rfl

/-- **A clean region holds no object** (`dead_childless`: an object meeting
a childless RAM untyped region is dead). -/
theorem JAtZ.mpEmpty {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcl : MpClean (L := L) Z H D s) {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) :
    (∀ q k, Z.th q = some k → q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 4096 ≤ q.val) ∧
    (∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val) := by
  obtain ⟨-, ⟨-, -, -, -, hI⟩, -⟩ := J.xtop.rel
  obtain ⟨hdt, hdh⟩ := dead_childless J.jcov J.ut hI hx hcx hnd
  rw [two_pow_asidPool] at hdt hdh
  obtain ⟨hD, -⟩ := hcl x hx p fi hcx hnd
  refine ⟨fun q k hq => ?_, fun q k hq => ?_⟩
  · by_contra hm; exact hm ((hD q (hdt q k hq hm).1).1 k hq)
  · by_contra hm; exact hm ((hD q (hdh q k hq hm).1).2 k hq)

/-- **The region `[p, p + 4096)` holds no object and no IPC-buffer word**
(`JAtZ.mpEmpty` and `MpClean`'s word clause at one cap; also after the
detype of the region, XTopJointMakePoolD): what the clean case's placement
lemmas (`JAtZ.mpOObjAt`, `JAtZ.mpPlacedCAt`, `JAtZ.mpRegionCAt`,
`JAtZ.mpAddOKAt`) need. -/
def MpEmptyAt (Z : XSets) (H : P1.Heap) (p : U64) : Prop :=
  (∀ q k, Z.th q = some k → q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 4096 ≤ q.val) ∧
  (∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val) ∧
  ∀ wp ∈ Z.B, (wp.1.val + 8 ≤ p.val ∨ p.val + 4096 ≤ wp.1.val) ∧
    ∀ i ∈ Fl4Spec.intUpto 0 7, (wp.2 + (7 - BitVec.ofInt 64 i)).toNat < p.val ∨
      p.val + 4096 ≤ (wp.2 + (7 - BitVec.ofInt 64 i)).toNat

/-- `MpEmptyAt` of a clean region (`JAtZ.mpEmpty`, `MpClean`). -/
theorem JAtZ.mpEmptyAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcl : MpClean (L := L) Z H D s) {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) : MpEmptyAt Z H p :=
  ⟨(J.mpEmpty arI hcl hx hcx hnd).1, (J.mpEmpty arI hcl hx hcx hnd).2, (hcl x hx p fi hcx hnd).2⟩

/-- **No `OObj` word in an empty region** (`JAtZ.mpOObj` from `MpEmptyAt`). -/
theorem JAtZ.mpOObjAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64} (hE : MpEmptyAt Z H p)
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false) :
    ∀ b : U64, p.val ≤ b.val → b.val < p.val + 4096 → ¬ Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b := by
  intro b h1 h2 hO
  obtain ⟨-, hHo, hB⟩ := hE
  have hks := J.jcov.ks x hx p _ fi hcx
  rw [two_pow_asidPool] at hks
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := by have := J.kern.cpuCs; rw [hc.cur] at this; exact this
  have hobj : ∀ {q : U64} {k : P1.HKind}, H q = some k → q.val ≤ b.val → b.val < q.val + 2 ^ k.bits → False :=
    fun {q k} hq l1 l2 => by have := hHo q k hq; omega
  obtain ⟨Tr, Cq, hP⟩ := J.jpl
  rcases hO with ⟨o1, o2⟩ | ⟨o1, o2⟩ | ⟨t, ht, o1, o2⟩ | ⟨e, he, o1, o2⟩ | ⟨r, hr, o1, o2⟩ | ⟨n, hn, o1, o2⟩ |
      ⟨q, hq, y, n, hk, o1, o2⟩ | ⟨wp, hw, o1, o2⟩
  · have := hks.2.1 Z.c hcC; omega
  · have := hks.1; omega
  · exact hobj (J.zH.1 t ht) (by omega) (by simp only [P1.HKind.bits]; omega)
  · exact hobj (J.zH.2.1 e he) (by omega) (by simp only [P1.HKind.bits]; omega)
  · exact hobj (J.zH.2.2.1 r hr) (by omega) (by simp only [P1.HKind.bits]; omega)
  · exact hobj (J.zH.2.2.2 n hn) (by omega) (by simp only [P1.HKind.bits]; omega)
  · exact hobj (hP.sc q y n (J.c0 q hq) hk).2 o1 (by
      simp only [P1.HKind.bits]
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.le_add_right n Fl4Spec.minSchedContextBits)
      omega)
  · have := (hB wp hw).1; omega

/-- **No `OObj` word in a clean region** (as ScPlaceUt's `oobj_childless`,
with `H` empty there and the buffer words off it by `MpClean`). -/
theorem JAtZ.mpOObj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcl : MpClean (L := L) Z H D s) {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) :
    ∀ b : U64, p.val ≤ b.val → b.val < p.val + 4096 → ¬ Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b :=
  J.mpOObjAt arI hx (J.mpEmptyAt arI hcl hx hcx hnd) hcx

set_option maxHeartbeats 1000000 in
/-- **`MpPlacedHyp` from `JAtZ` when the regions are clean** (as VsTopX's
`mpPlacedHyp_of`, from the dead-set cover `JCovD`: a clean region holds no
object, `JAtZ.mpEmpty`, so `restrictTh` keeps `th`, and no `OObj` word,
`JAtZ.mpOObj`). -/
theorem JAtZ.mpPlacedCAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {p : U64} (hE : MpEmptyAt Z H p) {x fi : U64} (hx : x ∈ Z.G.chains.flatten)
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (th' : TypedHeap) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit)
    (hth : th' = restrictTh Z.th p.val (p.val + 4096)) (hk : L.ksb s' = L.ksb s)
    (hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n))
    (hRg : MpRegion Z.th Z.G Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) p) :
    (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s' a' σ' →
      TopSR st th' (insert p Z.P) Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s' a' σ') ∧
    ∀ t : U64, Z.th t = some .tcb → th' t = some .tcb := by
  have hTh := hE.1
  have hrt : restrictTh Z.th p.val (p.val + 4096) = Z.th := by
    funext q
    unfold restrictTh
    split
    · rename_i hq
      cases hk' : Z.th q with
      | none => rfl
      | some k => have := hTh q k hk'; omega
    · rfl
  rw [hrt] at hth
  subst th'
  refine ⟨fun hS => ?_, fun t ht => ht⟩
  obtain ⟨hO, hTP⟩ := hS
  obtain ⟨hpal, hpfit, hp0, -, -, -, hPo, hLo, hTo⟩ := hRg
  have hout := hTh
  have hoob : ∀ b : U64, p.val ≤ b.val → b.val < p.val + 4096 → ¬ Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' b :=
    fun b h1 h2 hO' => J.mpOObjAt arI hx hE hcx b h1 h2 (Sched.OObj.mono hk hsc hO')
  have hpool : ∀ b, VsWrite (insert p Z.P) (L.ksb s') b → VsWrite Z.P (L.ksb s') b ∨
      (p.val ≤ b.val ∧ b.val < p.val + 4096 ∧ b.val % 8 = 0) := by
    rintro b (h | ⟨q, hq, lo, hl, rfl⟩)
    · exact Or.inl (Or.inl h)
    · rcases hq with rfl | hq
      · right; rw [peA_val hpfit hl]; refine ⟨by omega, by omega, by omega⟩
      · exact Or.inl (Or.inr ⟨q, hq, lo, hl, rfl⟩)
  refine ⟨hO, ⟨hTP.ep, ?_, hTP.pt, hTP.pl, fun b hb hv => ?_, hTP.nodeE, hTP.po, hTP.ps, fun b hb hw => ?_,
    fun b hw => ?_, fun b hw hsw => ?_, hTP.tko⟩⟩
  · -- `vs`
    refine ⟨hTP.vs.ksb_al, hTP.vs.ksb_fit, fun q hq => ?_, fun q hq => ?_⟩
    · rcases hq with rfl | hq
      · exact ⟨hpal, hpfit⟩
      · exact hTP.vs.pal q hq
    · rcases hq with rfl | hq
      · rw [hk]; exact hTo
      · exact hTP.vs.ptab q hq
  · -- `disj`
    rcases hv with h | h | ⟨q, hq, h1, h2'⟩ | h
    · exact hTP.disj b hb (Or.inl h)
    · exact hTP.disj b hb (Or.inr (Or.inl h))
    · rcases hq with (rfl | hq) | hq
      · exact hoob b h1 h2' hb
      · exact hTP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inl hq, h1, h2'⟩)))
      · exact hTP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inr hq, h1, h2'⟩)))
    · exact hTP.disj b hb (Or.inr (Or.inr (Or.inr h)))
  · -- `pv`
    rcases hpool b hw with h | ⟨h1, h2', -⟩
    · exact hTP.pv b hb h
    · obtain ⟨q, hq, i, hi, rfl⟩ := hb
      have hqa := hTP.pt q hq
      rw [peA_val (tbl_fit hqa) hi] at h1 h2'
      have := hLo q hq; omega
  · -- `vo`
    rcases hpool b hw with h | ⟨h1, h2', h8⟩
    · exact hTP.vo b h
    · refine ⟨h8, fun q k hq hin => ?_⟩
      have := hout q k hq; omega
  · -- `sd`
    rcases hpool b hw with h | ⟨h1, h2', -⟩
    · exact hTP.sd b h hsw
    · obtain ⟨y, hy, hb⟩ := hsw
      obtain ⟨q, i, hqi, rfl⟩ := hy
      have hv := hqi.val hTP.pl
      obtain ⟨k, hk', hs⟩ := hqi.size
      have := hout q k hk'
      have hf := hTP.pl.fits q k hk'
      rcases hb with rfl | rfl
      · rw [hv] at h1 h2'; omega
      · have : (core.num.U64.wrapping_add (slotOf q i) 8#u64).val = (slotOf q i).val + 8 := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; rw [hv]; omega
        rw [this, hv] at h1 h2'; omega

set_option maxHeartbeats 1000000 in
/-- **`MpPlacedHyp` from `JAtZ` when the regions are clean** (`JAtZ.mpPlacedCAt`
at each childless pool-sized untyped, `JAtZ.mpEmptyAt`). -/
theorem JAtZ.mpPlacedC {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcl : MpClean (L := L) Z H D s) :
    MpPlacedHyp st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s σ Z.G := by
  intro p th' s' a' σ' hth hk hsc hRg ⟨x, fi, hx, hcx, hnd⟩
  exact J.mpPlacedCAt arI (J.mpEmptyAt arI hcl hx hcx hnd) hx hcx th' s' a' σ' hth hk hsc hRg

/-- **The region facts of `MakePool`'s childless untyped from `JAtZ` when
the regions are clean** (what the old `JMpExtra` asked [J]): `MpRegion`
(alignment, fit and non-null pointer, no straddling object and no MDB slot
from `UtCapP3`; no CNode, pool or page table there: the region holds no
object of `th` or `H`, `JAtZ.mpEmpty`, and the spec's arch objects are `H`'s
`other` objects of at least a page, `SpecCover.arch`; the ASID table off it,
`UtKsApart`) and `RegOKTop` (`JAtZ.mpOObj`, the buffer bytes by
`MpClean`). -/
theorem JAtZ.mpRegionCAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs))
    (hidx : idx.length = rs) {p fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) (hE : MpEmptyAt Z H p) :
    MpRegion Z.th Z.G Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) p ∧ RegOKTop (L := L) Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ p := by
  obtain ⟨hPl, ⟨-, -, hM, hC, -⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hcx := capV_of_capAt hcap
  have hx : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hAs.isSlot, _, hcap, fun h => by cases h⟩
  have hnd := nodesc_of_cdt hPl hC hAs hnch
  have U := J.utc _ p _ fi false hAs hcap rfl
  have hTh := hE.1
  have hHo := hE.2.1
  have hks := J.jcov.ks _ hx p _ fi hcx
  rw [two_pow_asidPool] at hks
  have hpal : p.val % 4096 = 0 := by have := U.pal; rwa [two_pow_asidPool] at this
  have hpfit : p.val + 4096 ≤ 2 ^ 64 := by have := U.pfit; rwa [two_pow_asidPool] at this
  have hoff : ∀ q : U64, (∃ ao, σ.kheap q.bv = some (.archObj ao)) → q.val + 4096 ≤ p.val ∨ p.val + 4096 ≤ q.val := by
    rintro q ⟨ao, hq⟩
    obtain ⟨n, hn, hHq⟩ := J.cover.arch _ ao hq
    have h1 := hHo q _ hHq
    simp only [P1.HKind.bits] at h1
    have h2 : 4096 ≤ 2 ^ n := by
      calc 4096 = 2 ^ 12 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  have hR := J.xtop.fin.2.1
  have hPt := J.xtop.fin.2.2.1
  refine ⟨⟨hpal, hpfit, ?_, ?_, ?_, ?_, ?_, ?_, by have := hks.2.2; omega⟩, hpal, hpfit, J.mpOObjAt arI hx hE hcx,
    fun wp hw => (hE.2.2 wp hw).2⟩
  · intro e
    have hh := U.high (Sched.notDev_ram hcx)
    rw [e] at hh
    have h0 : (0#u64 : U64).val = 0 := rfl
    rw [h0] at hh
    norm_num at hh
  · have := U.nostr; rwa [two_pow_asidPool] at this
  · have := U.ns hnch; rwa [two_pow_asidPool] at this
  · rintro q r hq ⟨a1, a2⟩
    have := hTh q _ hq
    simp only [objSize] at this
    omega
  · intro q hq
    obtain ⟨f, hf, -⟩ := hR.pool q hq
    exact hoff q ⟨_, hf⟩
  · rintro q (hq | hq | hq | hq)
    · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact hoff q ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact hoff q ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact hoff q ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact hoff q ⟨_, hf⟩

/-- `JAtZ.mpRegionCAt` when the regions are clean (`JAtZ.mpEmptyAt`). -/
theorem JAtZ.mpRegionC {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcl : MpClean (L := L) Z H D s) {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs))
    (hidx : idx.length = rs) {p fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) :
    MpRegion Z.th Z.G Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) p ∧ RegOKTop (L := L) Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ p := by
  obtain ⟨hPl, ⟨-, -, hM, hC, -⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hx : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hAs.isSlot, _, hcap, fun h => by cases h⟩
  exact J.mpRegionCAt arI hpp hidx hcap hnch (J.mpEmptyAt arI hcl hx (capV_of_capAt hcap) (nodesc_of_cdt hPl hC hAs hnch))

/-- **The new pool's page joins `H` as an `other` object** (P1's
`AddOKP`, for `BlkOK.addOther`): a clean region holds no object of `H`
(`JAtZ.mpEmpty`), and RAM untyped regions miss the nodes and the
kernel-state block (`UtKsApart`). -/
theorem JAtZ.mpAddOKAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64} (hE : MpEmptyAt Z H p)
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (hpal : p.val % 4096 = 0) (hpfit : p.val + 4096 ≤ 2 ^ 64)
    (hp0 : p ≠ 0#u64) :
    P1.AddOKP st H (· = p) (.other 12) Cs s := by
  obtain ⟨-, hHo, -⟩ := hE
  have hks := J.jcov.ks x hx p _ fi hcx
  rw [two_pow_asidPool] at hks
  have h12 : (P1.HKind.other 12).bits = 12 := rfl
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq p' kp hp' => ?_,
    fun q q' hq hq' hne => absurd (hq.trans hq'.symm) hne, fun q hq c hc => ?_, fun q hq => ?_⟩
  · subst hq
    cases hk : H q with
    | none => rfl
    | some k =>
      have := hHo q k hk
      have := Nat.one_le_two_pow (n := k.bits)
      omega
  · subst hq; rw [h12]; exact hpal
  · subst hq; rw [h12]; exact hpfit
  · subst hq; exact hp0
  · subst hq; rw [h12, show (2:Nat) ^ 12 = 4096 from rfl]; have := hHo p' kp hp'; omega
  · subst hq; rw [h12]; exact hks.2.1 c hc
  · subst hq; rw [h12]; exact hks.1

/-- `JAtZ.mpAddOKAt` when the regions are clean (`JAtZ.mpEmptyAt`). -/
theorem JAtZ.mpAddOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcl : MpClean (L := L) Z H D s) {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) (hpal : p.val % 4096 = 0) (hpfit : p.val + 4096 ≤ 2 ^ 64)
    (hp0 : p ≠ 0#u64) :
    P1.AddOKP st H (· = p) (.other 12) Cs s :=
  J.mpAddOKAt arI hx (J.mpEmptyAt arI hcl hx hcx hnd) hcx hpal hpfit hp0

/-- **P1's `BlkOK` with the new pool's page in `H`** (`BlkOK.addOther`). -/
theorem JAtZ.mpBlk {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcl : MpClean (L := L) Z H D s) {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) (hpal : p.val % 4096 = 0) (hpfit : p.val + 4096 ≤ 2 ^ 64)
    (hp0 : p ≠ 0#u64) :
    let H' := H.add (· = p) (.other 12)
    P1.BlkOK st (P1.Heap.tcbs H') Cs (P1.Heap.omega H') H' (P1.Heap.frame H') (P1.Heap.replies H')
      (P1.Heap.scs H') (P1.Heap.ntfns H') (P1.Heap.scBits H') Ac s :=
  P1.BlkOK.addOther (J.mpAddOK arI hcl hx hcx hnd hpal hpfit hp0) J.kern.heap J.blk

/-! ## The front end's extra caps of the VSpace decodes (from `ExtraOK`) -/

/-- `vspace.extra` at an index below 3: the slot word, `none` when null. -/
theorem vsExtra_at (e : Aeneas.Std.Array obj.Slot 3#usize) (i : Usize) (hi : i.val < 3) (x : U64)
    (hx : Aeneas.Std.Array.index_usize e i = ok x) :
    vspace.extra e i = ok (if x = 0#u64 then none else some x) := by
  unfold vspace.extra
  have h3 : ¬ (i ≥ 3#usize) := by intro h; scalar_tac
  rw [if_neg h3, hx]
  simp only [bind_ok, obj.Slot.is_null]
  by_cases h : x = 0#u64 <;> simp [h]

/-- **`JVsExtra` from `ExtraOK`** (the front end's extra slots, `JAtZ.frontJ`):
no longer a premise of the table and frame paths. -/
theorem ExtraOK.vsExtra {Z : XSets} {s : S} {e : Aeneas.Std.Array obj.Slot 3#usize}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} (hP : Placed Z.th) (h : ExtraOK Z.th (L.mem s) e caps) :
    JVsExtra (L := L) Z s e caps := by
  have h0 := vsExtra_at e 0#usize (by decide) _ (exAt_idx0 e)
  obtain ⟨-, hs, hz⟩ := h
  cases caps with
  | nil =>
    have hz0 : exAt e 0 = 0#u64 := hz 0 (by simp) (by omega)
    rw [hz0, if_pos rfl] at h0
    exact ⟨Or.inl ⟨h0, rfl⟩, fun x hx => by rw [h0] at hx; exact absurd (eq_of_ok_eq hx) (by simp)⟩
  | cons y rest =>
    obtain ⟨hne, hS, -, cv, hc, -, hcr, -, -⟩ := srcOK_facts hP (hs 0 (by simp))
    rw [if_neg hne] at h0
    refine ⟨Or.inr ⟨_, cv, y.1, y.2, rest, h0, hc, hcr, rfl⟩, fun x hx => ?_⟩
    rw [h0] at hx
    have e0 : exAt e 0 = x := Option.some.inj (eq_of_ok_eq hx)
    rw [← e0]; exact hS

/-- **The ASID pool's extra cap from `ExtraOK`** (`JPoolPath`'s former
`hext` [W]). -/
theorem ExtraOK.poolExtra {Z : XSets} {s : S} {e : Aeneas.Std.Array obj.Slot 3#usize}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} (hP : Placed Z.th) (h : ExtraOK Z.th (L.mem s) e caps) :
    (vspace.extra e 0#usize = ok none ∧ caps = []) ∨
    ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
      (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), Z.th pc = some (.cnode r) ∧ idx.length = r ∧
      vspace.extra e 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
      capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ caps = (vc', (pc.bv, idx)) :: rest := by
  have h0 := vsExtra_at e 0#usize (by decide) _ (exAt_idx0 e)
  obtain ⟨-, hs, hz⟩ := h
  rcases caps with _ | ⟨⟨c0, q0, i0⟩, rest⟩
  · have hz0 : exAt e 0 = 0#u64 := hz 0 (by simp) (by omega)
    rw [hz0, if_pos rfl] at h0
    exact Or.inl ⟨h0, rfl⟩
  · obtain ⟨hne, -, hxa, cv, hc, -, hcr, -, ps, hps, hq⟩ := srcOK_facts hP (hs 0 (by simp))
    simp only [List.getElem_cons_zero] at hne hxa hc hcr hps hq
    subst hq
    rw [if_neg hne, hxa] at h0
    rw [hxa] at hc
    exact Or.inr ⟨ps, _, i0, cv, c0, rest, hps, rfl, h0, hc, hcr, rfl⟩

/-- **`JMpExtra` from `ExtraOK`** (no longer a premise of the ASID control
path). -/
theorem ExtraOK.mpExtra {Z : XSets} {s : S} {e : Aeneas.Std.Array obj.Slot 3#usize}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} (hP : Placed Z.th) (h : ExtraOK Z.th (L.mem s) e caps) :
    JMpExtra (L := L) Z s e caps := by
  have h0 := vsExtra_at e 0#usize (by decide) _ (exAt_idx0 e)
  have h1 := vsExtra_at e 1#usize (by decide) _ (exAt_idx1 e)
  obtain ⟨hlen, hs, hz⟩ := h
  have hS1 : ∀ y, vspace.extra e 1#usize = ok (some y) → IsSlot Z.th y := by
    intro y hy
    rw [h1] at hy
    by_cases hlt : 1 < caps.length
    · obtain ⟨hne, hS, -⟩ := srcOK_facts hP (hs 1 hlt)
      rw [if_neg hne] at hy
      have e1 : exAt e 1 = y := Option.some.inj (eq_of_ok_eq hy)
      rw [← e1]; exact hS
    · rw [hz 1 (by omega) (by omega), if_pos rfl] at hy
      exact absurd (eq_of_ok_eq hy) (by simp)
  refine ⟨hS1, ?_⟩
  by_cases hlt : 1 < caps.length
  · rcases caps with _ | ⟨⟨c0, q0, i0⟩, _ | ⟨⟨c1, sl1⟩, rest⟩⟩
    · simp at hlt
    · simp at hlt
    obtain ⟨hne0, -, hxa0, cv0, hc0, -, hcr0, -, ps, hps, hq⟩ := srcOK_facts hP (hs 0 (by simp))
    obtain ⟨hne1, -, -, cv1, hc1, -, hcr1, hcv1, -⟩ := srcOK_facts hP (hs 1 (by simp))
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hne0 hxa0 hc0 hcr0 hps hq hne1 hc1 hcr1
    subst hq
    rw [if_neg hne0, hxa0] at h0
    rw [if_neg hne1] at h1
    rw [hxa0] at hc0
    exact Or.inr ⟨ps, _, i0, exAt e 1, cv0, c0, cv1, c1, sl1, rest, hps, rfl, h0, h1, hc0, hcr0, hc1, hcr1, hcv1, rfl⟩
  · rw [hz 1 (by omega) (by omega), if_pos rfl] at h1
    exact Or.inl ⟨_, _, h0, h1, Or.inr rfl, by omega⟩

/-! ## The VSpace caps' paths (XTopJointEntry's `JPath`)

The labels are proved from `slbl = lbl.bv` (FrontEndLabel's `pt_label`,
`pd_label`, `pdpt_label`, `pml4_label`, `pool_label`, `frame_label`,
`getAddress_label`, `makePool_label`) and the extra caps from `ExtraOK`
(`ExtraOK.vsExtra`, `.poolExtra`, `.mpExtra`): the page table, page
directory, PDPT and PML4 paths ask nothing (XTopJointEntry's `JPath` is
`True` there). -/

/-- The ASID pool path: the extra cap native ([scope]: guest-root ASID
assignment, DESIGN §9). -/
structure JPoolPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  native : ∀ x, vspace.extra extra 0#usize = ok (some x) →
    ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va)

/-- The native frame path (FL4's EPT-map label is the [scope] case,
XTopJointEntry's `JPath`): `hno` [J] (l4v `valid_cap`: a large frame's range
against the other frame caps'). Every label at `J` with no per-op premise
(XTopJointVsSub's `decode_invocation_frameJS`). -/
structure JFramePath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (p : U64) (sz : capability.FrameSize) (rt : U64) (d m : Bool) (asid va : U64)
    (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  hno : sz = .Large → d = false → ∀ x ∈ Z.G.chains.flatten,
    Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
    (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
    Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x)

/-- The ASID control path: the cap is proved at `J` for any region
(MpDirtyJ's `decode_invocation_asid_controlJD`: FL4's restart, the drop of
the pool's frame at the restart's state, l4v's `delete_objects`, then the
clean case's step; the former `dirty` [W] removed, handoff/utj.md Round 15),
given the drop's premises, as the untyped path's (`JUtPath.heapH`,
`JUtPath.vsReach`). The label and extra caps are proved (`makePool_label`,
`ExtraOK.mpExtra`). -/
structure JAsidCPath (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop where
  /-- [J] `ArchFitHyp` and `RegionUnrefAt` at the entry's own `H`, `Cs`, `D`
  and state (as `JUtPath.heapH`): the drop's
  kept references and arch objects (`JAtZ.dropA`). -/
  heapH : ArchFitHyp H σ ∧ RegionUnrefAt (L := L) H Cs D s
  /-- [J] the drop's `VsReachMiss` (as `JUtPath.vsReach`; VsDrop, l4v
  `valid_vs_lookup` with `dead_childless`: no table reachable from the ASID
  table lies in a childless untyped cap's region), for a childless
  pool-sized RAM untyped cap's region at the restart's state, at the tables
  the slots' caps ask (`Vs.NeedR`). -/
  vsReach : ∀ (x p fi : U64) (s1 : S), x ∈ Z.G.chains.flatten →
    capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false → (∀ y, ¬ Mdb.Desc Z.G.par y x) →
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Vs.VsReachMiss p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) (L.mem s1) (L.ksb s1)
      (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
      (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1)

end

end

end Fl4Proofs.P3
