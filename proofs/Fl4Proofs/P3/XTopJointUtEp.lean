/-
P3 (DESIGN.md §9), untyped: **the retype of endpoints or notifications
without a reset, from `JAtZ`** (first pieces of XTopJointUt's `JUtRetHyp`,
handoff/utj.md "Round 2"/"Round 3").

* `retExp_pml4_back`: a PML4 cap in a slot after a retype whose new caps are
  no PML4 caps was there before (`RetExp`'s `gmem`/`newc`/`keep`/`utk`).
* `JAtZ.utEpXTop`: from `JAtZ` at the decode (no switch pending), a CNode
  slot's RAM untyped cap and the decode's `RetCtx` for types 2/3 without a
  reset, the restart and `untyped::retype` end done (`Ok`), the spec's
  restart and `invoke_untyped` deterministic, and `XTopAt` after at the
  sets of `JAtZ` with the new MDB ghost and the window's objects added to
  `Z.E` (type 2) or `Z.N` (type 3), `XSets.addW`: `XTopAt.addStep` (UtEpXTop)
  over `JAtZ.restartJ`'s `XTopAt`, the creation's slot-word frame
  (`RetFrame`), and the spec's outcome split by `invokeUntyped_noreset_add`
  (the window free in the spec's heap by `SpecFree`); then `XTopAt.addE`/
  `addN` with the window's words zero (`RetFrame`'s `WinZero`), its objects
  idle in the spec (`SpecAdd`, `KeepC`), and its words in no object
  (`JAtZ.free_noObj`).
* `JAtZ.free_noObj`: no word of a RAM untyped cap's free part is an `OObj`
  or `VObj` word of `JAtZ`'s sets (`UtKsApart` with its ASID-table clause,
  `UtCapP3.free`, `SpecFree`), the IPC-buffer words by `BufFreeHyp` [J].
* `BufFreeHyp` [J]: the IPC-buffer words `Z.B` miss the free part of every
  RAM untyped region (l4v `valid_untyped` with `valid_ipc_buffer_cap`;
  FL4's `lookup_ipc_buffer` reads inside the buffer slot's frame cap).
-/
import Fl4Proofs.P3.UtEpXTop
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.XTopJointUt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

theorem objTypeOf_ep {n : Nat} (h : objTypeOf n = some .endpointObject) : n = 2 := by
  unfold objTypeOf at h
  split_ifs at h <;> simp_all

theorem objTypeOf_ntfn {n : Nat} (h : objTypeOf n = some .notificationObject) : n = 3 := by
  unfold objTypeOf at h
  split_ifs at h <;> simp_all

/-- **A PML4 cap after a retype was there before** when no new cap is one
(the new caps are in new slots; old non-untyped caps are kept; an old
untyped cap stays untyped). -/
theorem retExp_pml4_back {th : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp th th m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th m' G')
    (hcj : ∀ j, j < w → ∀ p b a, cj j ≠ .Pml4 p b a) {x p : U64} {b : Bool} {asid : U64} (hxs : IsSlot th x)
    (hx : capAt m' x = ok (.Pml4 p b asid)) : capAt m x = ok (.Pml4 p b asid) := by
  have hmem' : x ∈ G'.chains.flatten := (hM'.members x).2 ⟨hxs, _, hx, by simp⟩
  have hv' := capV_of_capAt hx
  rcases hE.gmem x hmem' with hx0 | ⟨j, hj, rfl⟩
  · obtain ⟨-, c, hc, -⟩ := (hM.members x).1 hx0
    have hv := capV_of_capAt hc
    cases hu : isUt (capV m x)
    · have e := (hE.keep x hx0 hu).2
      rw [hv', hv] at e
      rw [hc, ← e]
    · have e := hE.utk x hx0 hu
      rw [hv'] at e; cases e
  · have e := hE.newc j hj
    rw [hv'] at e
    exact absurd e.symm (hcj j hj _ _ _)

/-- The window's object addresses: `A + j * k` for `j < w`. -/
def winSet (A k w : Nat) : Set U64 := {q | ∃ j, j < w ∧ q.val = A + j * k}

theorem winSet_bd {A k w : Nat} {q : U64} (h : q ∈ winSet A k w) :
    A ≤ q.val ∧ q.val + k ≤ A + w * k ∧ (A % k = 0 → q.val % k = 0) := by
  obtain ⟨j, hj, e⟩ := h
  have := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  refine ⟨by omega, by omega, fun h0 => ?_⟩
  rw [e, Nat.add_mul_mod_self_right]; exact h0

/-- `Z` with the MDB ghost `G'` and the window `W` added to the endpoints
(type 2) or to the notifications (otherwise). -/
def XSets.addW (Z : XSets) (nt : U64) (G' : MdbGhost) (W : Set U64) : XSets :=
  if nt.val = 2 then { Z with G := G', E := Z.E ∪ W } else { Z with G := G', N := Z.N ∪ W }

/-- An object of an SC's type has the SC's size (an SC of that size, or a
malformed CNode of the same garbage size). -/
theorem objBits_of_aType_sc {ko : Fl4Spec.KernelObject} {y : Fl4Spec.SchedContext} {n : Nat}
    (h : Fl4Spec.aType ko = Fl4Spec.aType (.schedContext y n)) :
    Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
  rcases sc_of_aType h with ⟨y0, rfl⟩ | ⟨sz, cs, rfl, hw⟩
  · simp only [Fl4Spec.objBits]; omega
  · simp only [Fl4Spec.aType, if_neg hw] at h
    split_ifs at h with h1
    all_goals first
      | cases h
      | (simp only [Fl4Spec.AType.aGarbage.injEq] at h; simp only [Fl4Spec.objBits]; omega)

/-- A field word of a window object is zero after the creation (`WinZero`,
not a TCB window). -/
theorem winZero_field {m : U64 → U64} {A k win : Nat} {T : Prop} (hz : WinZero m A k win T) (hT : ¬ T)
    {w : U64} (hw : w ∈ winSet A k win) (hal : w.val % 8 = 0) (hfit : w.val + k ≤ 2 ^ 64)
    {K : U64} (hK : K.val + 8 ≤ k) (hK8 : K.val % 8 = 0) : m (core.num.U64.wrapping_add w K) = 0#u64 := by
  obtain ⟨h1, h2, -⟩ := winSet_bd hw
  have hlt : w.val + K.val < 2 ^ 64 := by omega
  have hv : (core.num.U64.wrapping_add w K).val = w.val + K.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  rcases hz _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) with h | ⟨h, -⟩
  · exact h
  · exact absurd h hT

/-- **A range of the spec's memory is zero** (a RAM untyped cap's free part
`[lo, hi)` at the retype: the frame retype's new pages read zero, so `B`
grows there with `IpcRel.buf`; from `JEntryAt.urz`, or the reset's
`clear_memory`). -/
def UtFreeZ (σ : Fl4Spec.State Unit) (lo hi : Nat) : Prop :=
  ∀ a : Fl4Spec.Word, lo ≤ a.toNat → a.toNat < hi → σ.machineState.underlyingMemory a = 0

/-- **A RAM untyped region misses the 64 cores' node slots** of the
kernel-state block (`[ksb + 13568, ksb + 288000)`; `UtKsApart` asks only the
nodes of the cores of `Cs`). The frame retype's new `B` words must miss
every node (`JAtZ.nodeB`, all 64 cores). -/
def UtNodesAt (kb : U64) (p sb : U64) : Prop :=
  p.val + 2 ^ sb.val ≤ kb.val + 13568 ∨ kb.val + 288000 ≤ p.val

/-- **[J] Every RAM untyped region misses the 64 cores' node slots**
(`UtNodesAt` at every RAM untyped cap of the MDB slots). l4v:
`kernel_window`/`valid_untyped`: an untyped's range is free physical memory,
apart from the kernel's static data, here FL4's kernel-state block with all
`MAX_NODES` = 64 per-core nodes (`layout::ks::NODES` up to `ks::ASID_TABLE`,
statically allocated whatever the number of cores). True from boot (the untypeds are built from the free memory) and kept
by every step (child untypeds lie inside their parent's range). Not derivable
from `JAtZ`: `JCovD.ks` (`UtKsApart`) names only the nodes of `Cs`. -/
def UtNodesJ (m : U64 → U64) (G : MdbGhost) (kb : U64) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV m x = .Untyped p sb fi false → UtNodesAt kb p sb

/-- **[J] The IPC-buffer words miss the free part of every RAM untyped
region** (`B` at `m`, `G`). l4v: `valid_untyped` (an untyped cap's free part
`[p + fi, p + 2^sb)` holds no object) with `valid_ipc_buffer_cap` /
`tcb_cap_valid` (a thread's IPC buffer lies in the frame its buffer slot's
frame cap names, an object). FL4: `msg::lookup_ipc_buffer` returns a word
inside the non-device frame cap of the TCB's `SLOT_BUFFER`; that cap covers
the frame, and a covered range misses every untyped cap's free part
(`ut_free_fi`). Not derivable from `JAtZ`: nothing there ties `B` to a cap. -/
def BufFreeHyp (B : Set (U64 × Fl4Spec.Word)) (m : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ wp ∈ B, ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV m x = .Untyped p sb fi false →
    wp.1.val + 8 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ wp.1.val

/-- **[J] Every IPC-buffer word lies in a spec object** (l4v
`valid_ipc_buffer_cap` with `obj_at`: a thread's buffer lies in the data
page its buffer cap names; the ghost set `B` holds such words only: it is
fixed by every step at `J` and only the retype of frames would add words,
the reset's detype drop them). With `SpecFree` it gives `BufFreeHyp`
(`bufFree_of_obj`). -/
def BufObjHyp (B : Set (U64 × Fl4Spec.Word)) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ wp ∈ B, ∃ (o : Fl4Spec.ObjRef) (ko : Fl4Spec.KernelObject), σ.kheap o = some ko ∧ o.toNat ≤ wp.1.val ∧
    wp.1.val + 8 ≤ o.toNat + 2 ^ Fl4Spec.objBits ko

theorem bufFree_of_obj {B : Set (U64 × Fl4Spec.Word)} {m : U64 → U64} {G : MdbGhost} {σ : Fl4Spec.State Unit}
    (hF : Sched.SpecFree m G σ) (hO : BufObjHyp B σ) : BufFreeHyp B m G := by
  intro wp hw x hx p sb fi hc
  obtain ⟨o, ko, hk, h1, h2⟩ := hO wp hw
  rcases hF x hx p sb fi hc o ko hk with (h | h) | ⟨h3, h4⟩ <;> omega

/-! ### The buffer fields (`JBuf`) across a retype -/

/-- **Fresh objects added** (`SpecAdd`), none a TCB with an IPC frame or a
non-device data page: `IpcFrKeep`. -/
theorem IpcFrKeep.of_specAdd {σ σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop}
    {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject} (h : Sched.SpecAdd σ σ' W o)
    (ht : ∀ p, W p → ∀ x, o p = .tcb x → x.tcbIpcframe = .nullCap)
    (hd : ∀ p, W p → ∀ vms, o p ≠ .archObj (.dataPage false vms)) : IpcFrKeep σ σ' :=
  IpcFrKeep.of_fresh fun p => by
    by_cases hp : W p
    · obtain ⟨h1, h2⟩ := h.new p hp
      refine Or.inr ⟨h1, fun x hx => ht p hp x ?_, fun vms hv => hd p hp vms ?_⟩
      · rw [h2] at hx; exact Option.some.inj hx
      · rw [h2] at hv; exact Option.some.inj hv
    · exact Or.inl (h.old p hp)

/-- An untyped cap's `FrIn` (no condition). -/
theorem Vs.frIn_ut {U : Nat → Prop} {c : capability.Cap} (h : isUt c = true) : Vs.FrIn U c := by
  cases c <;> first | trivial | (simp [isUt] at h)

/-- **`FrSlots` across a retype** (`RetExp`): an old cap kept or an untyped
cap, a new cap `FrIn` by `hn`. -/
theorem Vs.FrSlots.retype {th th' th2 : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A0 k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64} {U U' : Nat → Prop}
    (h : Vs.FrSlots th U m) (hE : RetExp th th' m m' G G' A0 k w dslot cj xs)
    (hM : MdbLinks th m G) (hM' : MdbLinks th2 m' G') (hU : ∀ a, U a → U' a)
    (hn : ∀ j, j < w → Vs.FrIn U' (cj j)) : Vs.FrSlots th2 U' m' := by
  intro y hy
  by_cases hnull : capV m' y = .Null
  · rw [hnull]; trivial
  have hy' : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hy, _, capAt_capV m' y, hnull⟩
  rcases hE.gmem y hy' with hy0 | ⟨j, hj, rfl⟩
  · by_cases hu : isUt (capV m y) = true
    · exact Vs.frIn_ut (hE.utk y hy0 hu)
    · rw [(hE.keep y hy0 (by simpa using hu)).2]
      exact (h y ((hM.members y).1 hy0).1).mono hU
  · rw [hE.newc j hj]; exact hn j hj

/-- An untyped cap is native. -/
theorem Vs.nativeCap_ut {c : capability.Cap} (h : isUt c = true) : Vs.NativeCap c := by
  cases c <;> first | trivial | (simp [isUt] at h)

/-- A retype's new cap is native (`newCapOf` makes no VT-x cap). -/
theorem Vs.nativeCap_newCapOf (n : Nat) (base us : U64) (dev : Bool) : Vs.NativeCap (newCapOf n base us dev) := by
  have hf : ∀ sz, Vs.NativeCap (.Frame base sz 3#u64 dev false false 0#u64 0#u64) :=
    fun _ h => Bool.noConfusion h.1
  exact newCapOf_ind Vs.NativeCap n base us dev (fun _ => True.intro) (fun _ => True.intro) (fun _ => True.intro)
    (fun _ => True.intro) (fun _ => True.intro) (fun _ => True.intro) (fun _ => True.intro) (fun _ => True.intro)
    (fun _ => hf _) (fun _ => hf _) (fun _ => hf _) (fun _ => True.intro) (fun _ => True.intro) True.intro

/-- **`VsNat` across a retype** (`RetExp`; g2a, as `Vs.FrSlots.retype`): an
old cap kept or an untyped cap, a new cap native by `hn`. -/
theorem Vs.VsNat.retype {th th' th2 : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A0 k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (h : Vs.VsNat th m) (hE : RetExp th th' m m' G G' A0 k w dslot cj xs)
    (hM : MdbLinks th m G) (hM' : MdbLinks th2 m' G')
    (hn : ∀ j, j < w → Vs.NativeCap (cj j)) : Vs.VsNat th2 m' := by
  intro y hy
  by_cases hnull : capV m' y = .Null
  · rw [hnull]; trivial
  have hy' : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hy, _, capAt_capV m' y, hnull⟩
  rcases hE.gmem y hy' with hy0 | ⟨j, hj, rfl⟩
  · by_cases hu : isUt (capV m y) = true
    · exact Vs.nativeCap_ut (hE.utk y hy0 hu)
    · rw [(hE.keep y hy0 (by simpa using hu)).2]
      exact h y ((hM.members y).1 hy0).1
  · rw [hE.newc j hj]; exact hn j hj

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 1000000 in
/-- **No word of a RAM untyped cap's free part is an `OObj` or `VObj` word**
of `JAtZ`'s sets, at a later state with the same kernel-state base whose
SCs are the entry's (with their sizes): the node and the kernel-state block
and the ASID-table area by `UtKsApart`; TCBs, CNodes and TCB tables by
`UtCapP3.free`; endpoints, replies, notifications, SCs and VSpace tables are
spec objects (`SpecFree`); the IPC-buffer words by `BufFreeHyp` [J]. -/
theorem JAtZ.free_noObj {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot Z.th sl) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hBF : BufFreeHyp Z.B (L.mem s) Z.G) {s' : S} {σ' : Fl4Spec.State Unit} (hks : L.ksb s' = L.ksb s)
    (hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits)
    (b : U64) (h1 : p.val + fi.val ≤ b.val) (h2 : b.val < p.val + 2 ^ sb.val) :
    ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s') b := by
  have U := J.utc sl p sb fi false hAs hcap rfl
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, fun h => by cases h⟩
  have hcv := capV_of_capAt hcap
  obtain ⟨k1, k2, k3⟩ := J.jcov.ks _ hxm p sb fi hcv
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have k2c := k2 Z.c hcC
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hfi := U.fiLe
  have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hks]
  have spo : ∀ (o : U64) ko, σ.kheap o.bv = some ko → o.val ≤ b.val → b.val < o.val + 2 ^ Fl4Spec.objBits ko →
      False := by
    intro o ko hk g1 g2
    have := J.sfree _ hxm p sb fi hcv o.bv ko hk
    simp only [UScalar.bv_toNat] at this
    omega
  constructor
  · intro hO
    rcases hO with ⟨g1, g2⟩ | ⟨g1, g2, -⟩ | ⟨t, ht, g1, g2⟩ | ⟨e, he, g1, g2⟩ | ⟨r, hr, g1, g2⟩ | ⟨n, hn, g1, g2⟩ |
      ⟨q, hq, y, n, hk, hob⟩ | ⟨wp, hw, g1, g2⟩
    · rw [hnb] at g1 g2; omega
    · rw [hks] at g1 g2; omega
    · have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
      have := U.free t .tcb hth
      simp only [objSize] at this; omega
    · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.ep e he
      exact spo e _ hx g1 (by simp only [Fl4Spec.objBits, Fl4Spec.endpointBits]; omega)
    · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hr
      exact spo r _ hx g1 (by simp only [Fl4Spec.objBits, Fl4Spec.replyBits]; omega)
    · obtain ⟨x, hx, -⟩ := J.xtop.fin.1.1.2.2.1.ntfn n hn
      exact spo n _ hx g1 (by simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits]; omega)
    · obtain ⟨ko, hko, hbk⟩ := hsc q y n hk
      unfold Sched.ScObj at hob
      exact spo q ko hko hob.1 (by rw [hbk]; exact hob.2)
    · rcases hBF wp hw _ hxm p sb fi hcv with h | h <;> omega
  · intro hV
    rcases hV with ⟨q, r, hq, g1, g2⟩ | ⟨t, ht, g1, g2⟩ | ⟨q, hq, g1, g2⟩ | ⟨g1, g2⟩
    · have := U.free q _ hq; simp only [objSize] at this; omega
    · have := U.free t _ ht; simp only [objSize] at this; omega
    · rcases hq with hq | hq | hq | hq | hq
      · obtain ⟨f, hf, -⟩ := J.xtop.fin.2.1.pool q hq
        exact spo q _ hf g1 (by simp only [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.pageBits]; omega)
      · obtain ⟨f, hf, -⟩ := J.xtop.fin.2.2.1.l4 q hq
        exact spo q _ hf g1 (by simp only [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.tableSize,
          Fl4Spec.ptTranslationBits, Fl4Spec.wordSizeBits]; omega)
      · obtain ⟨f, hf, -⟩ := J.xtop.fin.2.2.1.l3 q hq
        exact spo q _ hf g1 (by simp only [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.tableSize,
          Fl4Spec.ptTranslationBits, Fl4Spec.wordSizeBits]; omega)
      · obtain ⟨f, hf, -⟩ := J.xtop.fin.2.2.1.l2 q hq
        exact spo q _ hf g1 (by simp only [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.tableSize,
          Fl4Spec.ptTranslationBits, Fl4Spec.wordSizeBits]; omega)
      · obtain ⟨f, hf, -⟩ := J.xtop.fin.2.2.1.l1 q hq
        exact spo q _ hf g1 (by simp only [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.tableSize,
          Fl4Spec.ptTranslationBits, Fl4Spec.wordSizeBits]; omega)
    · rw [hks] at g1 g2; omega

set_option maxHeartbeats 8000000 in
/-- **The no-reset retype of endpoints or notifications keeps `XTopAt` at
`JAtZ`'s sets** (module docstring). -/
theorem JAtZ.utEpXTop {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 2 ∨ nt.val = 3)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r false fiv)
    (hBF : BufFreeHyp Z.B (L.mem s) Z.G) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ1 σ' G',
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        (Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
          false)).run σ1 = ({(.ok (), σ')}, False) ∧
        XTopAt (L := L) AR (Z.addW nt G' (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat
          (2 ^ zOf nt.val us.val) win.val)) res.2.1 res.2.2 σ' ⦄ := by
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hU := J.utc _ p sb fi false hAs hcap rfl
  have hnd : Sched.NotDev (L.mem s) (cslotAddr (pp.bv, idx)) p sb fi := Sched.notDev_ram (capV_of_capAt hcap)
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, hFI0, -, hMO0, -⟩ := J.xtop.rel
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  have hty := hctx.ty
  have ht : t = .endpointObject ∨ t = .notificationObject := by
    rcases hnt with h | h <;> rw [h] at hty <;> simp [objTypeOf] at hty <;> simp [hty]
  have htU : t ≠ .untyped := by rcases ht with rfl | rfl <;> simp
  have htP : t ≠ .archObject .pml4Obj := by rcases ht with rfl | rfl <;> simp
  have htT : t ≠ .tcbObject := by rcases ht with rfl | rfl <;> simp
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  have hfiv : fiv = fi := by rw [hctx.fidx]; rfl
  subst hfiv
  have hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fiv.val = 0 := fun hnc => by
    have e := hctx.resetEq; simp [hnc] at e
  -- the restart, at `J` and at the CSpace
  obtain ⟨s1, σ1, -, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hk1, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hksz : KSz σ σ1 := ksz_of_eq (nkz_setThreadState _ _) hst1
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by rcases hnt with h | h <;>
    simp [zOf, h]) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_cont_all (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig (L.curW s)
    J.kern.cur hct J.kern.curT J.kern.act hpp hidx hcap hU.pal hU.pfit hU.fiLe (hU.high hnd)
    (fun h => (hU.actZ hnd) ⟨by omega, h.2⟩) hU.free (hU.zero hnd) hunused Fl4Spec.fl4ObjBitsApi nt us dest off win t r
    false fiv (by omega) hb J.kern.dwAl J.kern.dwObj (fun h => (hU.dwReg hnd) ⟨by omega, h.2⟩) J.kern.dwNe J.kern.head
    hctx) (fun res hRP => ?_)
  obtain ⟨hok, har, σ1'', hst, σ', G', th', hrun, -, hR', hV', hM', hC', hI', -, hSt, hFin, hks, Aw, k, w, dslot, cj,
    hE, hRF, -⟩ := hRP
  have e1 : σ1'' = σ1 := by
    have e := congrArg Prod.fst (hst.symm.trans hst1)
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at e
    exact e
  subst σ1''
  obtain ⟨ct0, s0, hct0, hs0, hbr⟩ := hRF
  rw [hct] at hct0; cases eq_of_ok_eq hct0
  rw [hs1] at hs0; cases eq_of_ok_eq hs0
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, -⟩, sR, thR, lo, hi, hor, -, -, -, -, ⟨n0, hn0, hThX, uu, -, hcj⟩, -,
    hW, hWZ, -⟩
  · rw [hok] at e; cases e
  have hsR : sR = s1 ∧ thR = Z.th := by
    rcases hor with ⟨h1, h2, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h1, h2⟩
    · cases hRB
  obtain ⟨e2, e3⟩ := hsR
  subst sR
  subst thR
  have hn0v : n0 = nt.val := by
    rcases ht with rfl | rfl
    · rw [objTypeOf_ep hn0]; rcases hnt with h | h <;> rw [h] at hty <;> simp [objTypeOf] at hty ⊢ <;> omega
    · rw [objTypeOf_ntfn hn0]; rcases hnt with h | h <;> rw [h] at hty <;> simp [objTypeOf] at hty ⊢ <;> omega
  subst hn0v
  have hk0 : thKindN nt.val us.val = none := by
    unfold thKindN; rw [if_neg (by omega), if_neg (by omega)]
  have hth : th' = Z.th := funext fun q => by rw [hThX.1 q, hk0]; simp
  subst hth
  -- FL4's writes: slot words
  have hw : P1.WritesIn st s1 res.2.1 (Sched.SlotWd Z.th) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨h1, -⟩
    · exact absurd h1 htT
    · exact Sched.slotSpan_wd hP hb h
    · exact absurd h1 htP))⟩
  -- the spec's outcome: the window's objects added, then CNodes changed
  have hSR1 := J1.xtop.rel.2.1.1
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  obtain ⟨-, σB, hA, hcnk, hkc⟩ := invokeUntyped_noreset_add Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ1 htU htP {pp.bv, dest.bv} (Or.inl rfl)
    (fun d hd => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
      exact Or.inr rfl)
    (by
      rintro q (rfl | hq)
      · obtain ⟨cs, h, -⟩ := hSR1.cnode pp rs hpp; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hq]; obtain ⟨cs, h, -⟩ := hSR1.cnode dest r hctx.cnode.1; exact ⟨r, cs, h⟩)
    (by
      intro q hq
      rw [hlen] at hq
      obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
      rw [hb] at hq ⊢
      have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have hfit := hU.pfit
      have hqv := ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (n := j * 2 ^ zOf nt.val us.val) (by have := Nat.one_le_two_pow (n := zOf nt.val us.val); omega)
      cases hq1 : σ1.kheap (Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
          (j * 2 ^ zOf nt.val us.val)) with
      | none => rfl
      | some ko =>
        exfalso
        obtain ⟨ko0, hko0, -⟩ := hksz _ _ hq1
        have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
        have h1 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko0)
        have hz1 := Nat.one_le_two_pow (n := zOf nt.val us.val)
        rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap) _ ko0 hko0 with h | ⟨h2, h3⟩
        · rw [hqv] at h; omega
        · rw [hqv] at h2 h3; omega)
    (.ok (), σ') (by rw [hrun]; rfl)
  have ho : ∀ q, q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∀ x n, Fl4Spec.defaultObject t false us.val σ1.curDomain ≠ .schedContext x n := by
    intro q _ x n; rcases ht with rfl | rfl <;> simp [Fl4Spec.defaultObject]
  have hks1 : L.ksb s1 = L.ksb s := hk1
  have hcjne : ∀ j, j < w → ∀ p b a, cj j ≠ .Pml4 p b a := by
    intro j _ p b a
    rw [hcj]
    rcases hnt with h | h <;> simp [cjOf, newCapOf, h]
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s1) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    rw [hSS1.capAt hxs]
    exact retExp_pml4_back hE hM hM' hcjne hxs hc
  have hX' := XTopAt.addStep J1.xtop hw hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (by rw [hks1]; exact hSt.okv hMO0) hTS
  refine ⟨hok, har, σ1, σ', G', hst1, hrun, ?_⟩
  rw [har]
  -- the window's objects, added to `E` or `N` (`XTopAt.addE`/`addN`)
  have hksR : L.ksb res.2.1 = L.ksb s := hw.1.trans hks1
  have hnbR : L.nodeBase res.2.1 Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hksR]
  have hfit := hU.pfit
  have hhigh := hU.high hnd
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨k1, k2, -⟩ := J.jcov.ks _ hxG p sb fiv (capV_of_capAt hcap)
  obtain ⟨Q0, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have k2c := k2 Z.c hcC
  obtain ⟨Tr, Cq, hJp⟩ := J.jpl
  have hwb : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), p.val + fiv.val ≤ q.val ∧ q.val + 2 ^ (zOf nt.val us.val) ≤ p.val + 2 ^ sb.val ∧ q.val % 2 ^ (zOf nt.val us.val) = 0 := by
    intro q hq
    obtain ⟨b1, b2, b3⟩ := winSet_bd hq
    exact ⟨by omega, by omega, b3 hA2⟩
  have hreg : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) := by
    intro q hq
    obtain ⟨j, hj, e⟩ := hq
    rw [hlen, hb]
    unfold regionPtrs
    refine List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩
    have hjk : (j + 1) * 2 ^ (zOf nt.val us.val) ≤ win.val * 2 ^ (zOf nt.val us.val) := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have := Nat.one_le_two_pow (n := zOf nt.val us.val)
    apply BitVec.eq_of_toNat_eq
    beta_reduce
    rw [ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (n := j * 2 ^ (zOf nt.val us.val))
      (by omega)]
    simp only [UScalar.bv_toNat]
    omega
  have hspec : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), σ'.kheap q.bv = some (Fl4Spec.defaultObject t false us.val σ1.curDomain) := by
    intro q hq
    have hB := (hA.new _ (hreg q hq)).2
    rcases hkc q.bv with e | ⟨r0, cs, cs', e1, -⟩
    · exact e.trans hB
    · have e2 := hB.symm.trans e1
      rcases ht with rfl | rfl <;> simp [Fl4Spec.defaultObject] at e2
  have hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    have hBk : σB.kheap q.bv = some (.schedContext y n) := by
      rcases hkc q.bv with e | ⟨r0, cs, cs', -, e2⟩
      · exact e.symm.trans hq
      · have e3 := e2.symm.trans hq; cases e3
    by_cases hWq : q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val)
    · rw [(hA.new _ hWq).2] at hBk
      rcases ht with rfl | rfl <;> simp [Fl4Spec.defaultObject] at hBk
    · rw [hA.old _ hWq] at hBk
      obtain ⟨ko, hko, hty⟩ := hksz _ _ hBk
      exact ⟨ko, hko, objBits_of_aType_sc hty⟩
  have hfr0 := J.free_noObj hAs hcap hBF hksR hsc
  have hWZ' : WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val (t = .tcbObject) := by
    have h0 := hWZ ⟨rfl, htP⟩
    rw [eA, ek, ew, hlen, hb] at h0
    exact h0
  have hTn : ¬ t = .tcbObject := htT
  have hTT : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), ∀ t0 ∈ Z.T, t0.val + 4096 ≤ q.val ∨ q.val + 2 ^ (zOf nt.val us.val) ≤ t0.val := by
    intro q hq t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hU.free t0 .tcb hth
    obtain ⟨b1, b2, -⟩ := hwb q hq
    simp only [objSize] at this; omega
  have hpos : 0 < 2 ^ (zOf nt.val us.val) := Nat.two_pow_pos _
  unfold XSets.addW
  split_ifs with h2
  · -- endpoints
    have htE : t = .endpointObject := by
      rcases ht with rfl | rfl
      · rfl
      · have := objTypeOf_ntfn hn0; omega
    have hz4 : zOf nt.val us.val = 4 := by simp [zOf, h2]
    have h16 : (2 : Nat) ^ (zOf nt.val us.val) = 16 := by rw [hz4]; rfl
    exact XTopAt.addE hX' (Wn := (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val))
      (fun e he => by rw [hspec e he, htE]; rfl)
      (fun e he => by
        obtain ⟨b1, b2, b3⟩ := hwb e he
        rw [h16] at b2 b3
        rw [Notif.epTSA_eq, Notif.epHeadA_eq]
        refine ⟨winZero_field hWZ' hTn he (by omega) (by omega) (by rw [h16]; simp) (by simp),
          winZero_field hWZ' hTn he (by omega) (by omega) (by rw [h16]; simp) (by simp)⟩)
      (fun e he => by obtain ⟨b1, b2, b3⟩ := hwb e he; rw [h16] at b2 b3; exact ⟨b3, by omega, by omega⟩)
      (fun e he t0 ht0 => by have := hTT e he t0 ht0; rw [h16] at this; exact this)
      (fun e he => by obtain ⟨b1, b2, -⟩ := hwb e he; rw [h16] at b2; rw [hksR]; omega)
      (fun e he b g1 g2 => by obtain ⟨b1, b2, -⟩ := hwb e he; rw [h16] at b2; exact hfr0 b (by omega) (by omega))
  · -- notifications
    have h3 : nt.val = 3 := hnt.resolve_left h2
    have htN : t = .notificationObject := by
      rcases ht with rfl | rfl
      · have := objTypeOf_ep hn0; omega
      · rfl
    have hz6 : zOf nt.val us.val = 6 := by simp [zOf, h3]
    have h64 : (2 : Nat) ^ (zOf nt.val us.val) = 64 := by rw [hz6]; rfl
    exact XTopAt.addN hX' (Wn := (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val))
      (fun n hn => by rw [hspec n hn, htN]; rfl)
      (fun n hn => by
        obtain ⟨b1, b2, b3⟩ := hwb n hn
        rw [h64] at b2 b3
        rw [Notif.epTSA_eq, Notif.epHeadA_eq, Notif.nBoundA_eq, Notif.nScA_eq]
        refine ⟨winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
          winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
          winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
          winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp)⟩)
      (fun n hn => by obtain ⟨b1, b2, b3⟩ := hwb n hn; rw [h64] at b2 b3; exact ⟨b3, by omega⟩)
      (fun n hn t0 ht0 => by have := hTT n hn t0 ht0; rw [h64] at this; exact this)
      (fun n hn => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; rw [hnbR]; omega)
      (fun n hn => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; rw [hksR]; omega)
      (fun n hn b g1 g2 => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; exact hfr0 b (by omega) (by omega))

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` at enlarged sets and a grown heap** (the variant of
`JAtZ.cs_frameV` for a retype's endpoints or notifications, `XSets.addW`,
with `H` grown by the window's objects): `XTopAt`, the CSpace fields (`JCs`)
and the re-established fields (`JRest`) at the new sets `Z'` and heap `H'`;
the fields that read the enlarged sets or `H'` given (`ks`, `thT`, `ip`,
`nk`, `cover`, `obj`, `zH`, `hset`, `hscC`); the rest from `J` (`Z'` keeps
`Z`'s typed heap, SCs and buffer words, the kernel-state base kept).
`SchedValid` and the spec's links rebuilt as in `cs_frameV`. -/
theorem JAtZ.add_frame {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64}
    (hth : Z'.th = Z.th) (hC : Z'.C = Z.C) (hB : Z'.B = Z.B) (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR Z' s' a' σ') (hCs : JCs (L := L) Z' s' σ') (R : JRest (L := L) arI Z' H' Cs Ac' Lst' D' s' σ')
    (hKs : KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s')) (hthT : ∀ t, Z'.th t = some .tcb → t ∈ Z'.T)
    (hIp : IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B)
    (hnk : ∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val)
    (hcov : Sched.SpecCover H' σ') (hobj : Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ')
    (hzH : (∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn))
    (hset : (∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R))
    (hscC : ∀ c z, H' c = some (.sc z) → c ∈ Z'.C)
    (hvc : Vs.VsSlotsW Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 (L.mem s'))
    (hbf : JBuf (L := L) Z' s' σ') (hext : JExt (L := L) Z'.th s')
    (hlv : LiveDN (L := L) Z'.th H' Cs Z'.G s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z'.th s', p ∈ D') :
    JAtZ (L := L) arI AR Z' H' Cs Ac' Lst' D' s' a' σ' := by
  have hTe : Z'.T = P1.Heap.tcbs H' := by
    obtain ⟨Tr, Cq, hJ⟩ := R.jpl
    exact Set.ext fun t => ⟨fun h => hzH.1 t h, fun h => hthT t ((hJ.tcb t).2 h)⟩
  have hRe : Z'.R = P1.Heap.replies H' := Set.ext fun r => ⟨fun h => hzH.2.2.1 r h, fun h => hset.2.2 r h⟩
  have hc0 : ∀ q ∈ Z'.C, q ≠ 0#u64 := by rw [hC]; exact J.c0
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX hTe hobj R.blk hset.2.1 R.jpl hc0
  exact ⟨hX, R.call, R.rfree, R.rrecv, R.yld, R.mcp, R.buf, hKs, hthT, by rw [hth]; exact J.thk, hIp, R.rp, R.apart,
    hnk, fun wp hw c hc => by
      simp only [P1.LawfulStore.nodeBase, hks]; rw [hB] at hw; exact J.nodeB wp hw c hc,
    R.jpl, hcov, hobj, hzH, hCs.sfree, hset, hscC, R.jcov,
    R.kern, hCs.del, hCs.ut, by rw [hth]; exact J.bound, hCs.finM, R.utc, R.nsc, R.inv, R.cur, R.own, R.off, R.act,
    hc0, R.bsa, schedValid_rebuild hX hTe hRe hobj R.blk hset.1 hset.2.1 R.call R.yld hc0 R.inv hsl, R.isorted, hsl,
    R.curRun, R.blk, by rw [hth, hks]; exact J.intL, hvc, hbf.1, hbf.2.1, hbf.2.2, hext, hlv, hzD⟩


set_option maxHeartbeats 1000000 in
/-- **`JAtZ.add_frame` with `B` changed** (the frame retype, UtFrameAdd): the
IPC-buffer words' node apartness `hnB` given at the new `Z'.B`.

**`JAtZ` at enlarged sets and a grown heap** (the variant of
`JAtZ.cs_frameV` for a retype's endpoints or notifications, `XSets.addW`,
with `H` grown by the window's objects): `XTopAt`, the CSpace fields (`JCs`)
and the re-established fields (`JRest`) at the new sets `Z'` and heap `H'`;
the fields that read the enlarged sets or `H'` given (`ks`, `thT`, `ip`,
`nk`, `cover`, `obj`, `zH`, `hset`, `hscC`); the rest from `J` (`Z'` keeps
`Z`'s typed heap, SCs and buffer words, the kernel-state base kept).
`SchedValid` and the spec's links rebuilt as in `cs_frameV`. -/
theorem JAtZ.add_frameB {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64}
    (hth : Z'.th = Z.th) (hC : Z'.C = Z.C) (hks : L.ksb s' = L.ksb s)
    (hnB : ∀ wp ∈ Z'.B, ∀ c : U64, c.val < 64 → wp.1.val + 8 ≤ L.nodeBase s' c ∨ L.nodeBase s' c + 4288 ≤ wp.1.val)
    (hX : XTopAt (L := L) AR Z' s' a' σ') (hCs : JCs (L := L) Z' s' σ') (R : JRest (L := L) arI Z' H' Cs Ac' Lst' D' s' σ')
    (hKs : KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s')) (hthT : ∀ t, Z'.th t = some .tcb → t ∈ Z'.T)
    (hIp : IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B)
    (hnk : ∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val)
    (hcov : Sched.SpecCover H' σ') (hobj : Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ')
    (hzH : (∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn))
    (hset : (∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R))
    (hscC : ∀ c z, H' c = some (.sc z) → c ∈ Z'.C)
    (hvc : Vs.VsSlotsW Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 (L.mem s'))
    (hbf : JBuf (L := L) Z' s' σ') (hext : JExt (L := L) Z'.th s')
    (hlv : LiveDN (L := L) Z'.th H' Cs Z'.G s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z'.th s', p ∈ D') :
    JAtZ (L := L) arI AR Z' H' Cs Ac' Lst' D' s' a' σ' := by
  have hTe : Z'.T = P1.Heap.tcbs H' := by
    obtain ⟨Tr, Cq, hJ⟩ := R.jpl
    exact Set.ext fun t => ⟨fun h => hzH.1 t h, fun h => hthT t ((hJ.tcb t).2 h)⟩
  have hRe : Z'.R = P1.Heap.replies H' := Set.ext fun r => ⟨fun h => hzH.2.2.1 r h, fun h => hset.2.2 r h⟩
  have hc0 : ∀ q ∈ Z'.C, q ≠ 0#u64 := by rw [hC]; exact J.c0
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX hTe hobj R.blk hset.2.1 R.jpl hc0
  exact ⟨hX, R.call, R.rfree, R.rrecv, R.yld, R.mcp, R.buf, hKs, hthT, by rw [hth]; exact J.thk, hIp, R.rp, R.apart,
    hnk, hnB,
    R.jpl, hcov, hobj, hzH, hCs.sfree, hset, hscC, R.jcov,
    R.kern, hCs.del, hCs.ut, by rw [hth]; exact J.bound, hCs.finM, R.utc, R.nsc, R.inv, R.cur, R.own, R.off, R.act,
    hc0, R.bsa, schedValid_rebuild hX hTe hRe hobj R.blk hset.1 hset.2.1 R.call R.yld hc0 R.inv hsl, R.isorted, hsl,
    R.curRun, R.blk, by rw [hth, hks]; exact J.intL, hvc, hbf.1, hbf.2.1, hbf.2.2, hext, hlv, hzD⟩

end

end

end Fl4Proofs.P3
