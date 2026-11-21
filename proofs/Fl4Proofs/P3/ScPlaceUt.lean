/-
P3 (DESIGN.md §9): **the joint placement invariant against untyped
memory**: a childless untyped cap's region holds no object of the typed
heaps, nor any word the other subsystems' relations read (for MakePool's
`MpPlacedHyp`, and retype).

* `Covered mem G lo hi`: the bytes `[lo, hi)` lie in the range of a
  physical, non-untyped cap of the MDB.
* `JCov th H G Cs s`: every object of `th` and of P1's heap `H` is
  covered (l4v: objects are named by caps; the ghost heaps track the
  objects with caps), and the RAM untyped caps' ranges miss the
  kernel-state block and the core nodes (`UtKsApart`; not device untypeds,
  losfair/FL4#34).
* `ut_free`: a covered range misses a childless untyped cap's range
  (`UtInv.drange`, `MdbInv.anc_ut`).
* `restrictTh_childless`: so `restrictTh th p (p + 2 ^ sb) = th`
  (MpPlacedHyp's (b)); `oobj_childless`: no `OObj` word lies there
  (MpPlacedHyp's (a) at the entry state), and `OObj.mono` carries it to an
  outcome with the kernel-state base kept and no new SC.
## Open design question: keeping `JCov`

`JCov` asks every ghost object to be named by a cap. Deleting the last cap
of an object breaks it unless the ghost heaps drop the object, and every
theorem that fixes `th` (or P1's sets) across a step then has to re-index.
The options:

1. **Ghost heaps shrink on the last cap's deletion.** `th`, `H` and P1's
   sets become per-state (`∃ th' H'` in every post, as `TopPostM` already
   has `∃ th' G'`). Cost: the largest. P1's entry theorem fixes its sets
   across entries, and every delete, revoke and finalisation proof (CSpace,
   P1 `QueueFin*`, `FinWorkHyp`) would carry a re-indexing; the TCB, SC and
   endpoint relations would have to drop the object too.
2. **Monotone ghost heaps with a dead set** (recommended). Deletion marks
   the object dead (a ghost set `D`, no reader: not queued, not current, no
   cap) and changes nothing else; `JCov` asks each object to be covered or
   dead. The childless-untyped lemma then shows only dead objects lie in a
   retyped region, and only retype (which already changes `th`, through
   `restrictTh`) removes them, from `th`, `H` and P1's sets. Cost: one
   ghost set; P1's invariants need "a dead object is read by nothing", kept
   by the finalisations (they already clear the queues and bindings); the
   re-indexing happens at retype only, where it is already done.
3. **No ghost liveness, l4v's `valid_untyped` instead**: objects meeting an
   untyped's range lie in it and outside its free part, and every object
   lies in some untyped range. Cost: stale objects below the free index
   stay allowed, so MakePool and retype still have to remove them from
   P1's sets and from the other relations (option 2's re-indexing, without
   a name for the objects being removed), and the "some untyped range"
   part needs the boot-time objects' untyped caps.

Recommendation: option 2. It localizes the re-indexing to retype and
makes the removed objects explicit.
-/
import Fl4Proofs.P3.ScPlace
import Fl4Proofs.P3.UntypedUtOps
import Fl4Proofs.P3.UntypedReset
import Fl4Proofs.P3.VsTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

/-- The bytes `[lo, hi)` lie in the range of a physical, non-untyped cap. -/
def Covered (mem : U64 → U64) (G : MdbGhost) (lo hi : Nat) : Prop :=
  ∃ y ∈ G.chains.flatten, physF (capV mem y) = true ∧ isUt (capV mem y) = false ∧
    baseF (capV mem y) ≤ lo ∧ hi ≤ topF (capV mem y) + 1

/-- **A covered range misses a childless untyped cap's range.** -/
theorem ut_free {mem : U64 → U64} {G : MdbGhost} (hU : UtInv mem G) (hI : MdbInv mem G) {x : U64}
    (hx : x ∈ G.chains.flatten) {p sb fi : U64} {d : Bool} (hcx : capV mem x = .Untyped p sb fi d)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x) {lo hi : Nat} (hlh : lo < hi) (hc : Covered mem G lo hi) :
    hi ≤ p.val ∨ p.val + 2 ^ sb.val ≤ lo := by
  obtain ⟨y, hy, hp, hut, hb, ht⟩ := hc
  have hsb := capV_ut_sb hcx
  have hreg := hU.reg x hx (by rw [hcx]; exact ok_inj (phys_eq _).symm)
  rw [hcx] at hreg
  obtain ⟨b1, t1, -⟩ := ut_range hsb hreg
  have hyx : y ≠ x := by rintro rfl; rw [hcx] at hut; cases hut
  by_cases hdj : Disj (capV mem y) (capV mem x)
  · unfold Disj at hdj
    rw [hcx, b1, t1] at hdj
    have := Nat.one_le_two_pow (n := sb.val)
    omega
  · rcases hU.drange x hx p sb fi d hcx y hy hyx hp hdj with h | h
    · exact absurd h (hnd y)
    · have := hI.anc_ut h (by rw [hcx]; rfl)
      rw [hut] at this; cases this

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The current core's idle objects**: its idle thread (`L.idleW`, the
node's `IDLE_THREAD` word) and its idle SC (`idleScW`, the node's `IDLE_SC`
word, which is the spec's `idle_sc` by `SchedSpec.idleSc`). FL4's boot
(`create_idle_threads`) gives them no cap, so `JCov` exempts them from its
cover (l4v: the idle thread is a global reference, not named by a cap,
`valid_global_refs`). Only the current core's: `H`'s TCBs are `Z.T`'s, all
of affinity `Z.c` (`SchedCore.aff`), and the spec's `idle_sc` is this
core's idle SC. -/
def IdleAt (s : S) (q : U64) : Prop := q = L.idleW s ∨ q = idleScW (L := L) s

/-- **An object inside the kernel-state block** (`[lo, hi)` within
`[ksb, ksb + 13568)`): the IRQ node's one-slot CNodes (`IntLayout.node`)
and the rest of the block, which `H` holds as `other` objects (P1's
`SgOK.ksΩ` puts every block word in `Ω = Heap.omega H`). No cap names
them (l4v `valid_global_refs`: the IRQ node and the kernel's globals are
global references), so `JCov` exempts them from its cover, as `IdleAt`. -/
def KsIn (s : S) (lo hi : Nat) : Prop := (L.ksb s).val ≤ lo ∧ hi ≤ (L.ksb s).val + 13568

/-- **The objects at `q` lie inside the kernel-state block** (`KsIn`, of
`th`'s and of `H`'s object there). -/
def KsObj (th : TypedHeap) (H : Heap) (s : S) (q : U64) : Prop :=
  (∀ k, th q = some k → KsIn (L := L) s q.val (q.val + max (objSize k) 1)) ∧
  (∀ k, H q = some k → KsIn (L := L) s q.val (q.val + 2 ^ k.bits))

/-- **An object `JCov` exempts from its cover**: an idle object (`IdleAt`)
or one inside the kernel-state block (`KsObj`). -/
def ExAt (th : TypedHeap) (H : Heap) (s : S) (q : U64) : Prop := IdleAt (L := L) s q ∨ KsObj (L := L) th H s q

/-- The idle words (`IdleAt`'s) kept from `s` to `s'`. -/
def IdleKeep (s s' : S) : Prop := L.idleW s' = L.idleW s ∧ idleScW (L := L) s' = idleScW (L := L) s

theorem IdleKeep.refl (s : S) : IdleKeep (L := L) s s := ⟨rfl, rfl⟩

theorem IdleKeep.trans {s1 s2 s3 : S} (h1 : IdleKeep (L := L) s1 s2) (h2 : IdleKeep (L := L) s2 s3) :
    IdleKeep (L := L) s1 s3 := ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem exAt_of {th : TypedHeap} {H : Heap} {s s' : S} (hidl : IdleKeep (L := L) s s') (hks : L.ksb s' = L.ksb s)
    {q : U64} : ExAt (L := L) th H s' q ↔ ExAt (L := L) th H s q := by
  unfold ExAt IdleAt KsObj KsIn; rw [hidl.1, hidl.2, hks]

/-- **The idle objects lie outside every RAM untyped region** (l4v
`valid_global_refs` for untyped caps: no cap's range holds a global
object): the idle address is outside each non-device untyped cap's region,
and so are the typed-heap and `H` objects at it. Not asked of device
untypeds: since losfair/FL4#34 a device untyped's pointer
`paddr + PPTR_BASE` may lie in the kernel image, where the idle objects
are. -/
def IdleOut (th : TypedHeap) (H : Heap) (G : MdbGhost) (s : S) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV (L.mem s) x = .Untyped p sb fi false → ∀ q, IdleAt (L := L) s q →
    (q.val < p.val ∨ p.val + 2 ^ sb.val ≤ q.val) ∧
    (∀ k, th q = some k → q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val) ∧
    (∀ k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val)

theorem idleAt_of {s s' : S} (hidl : IdleKeep (L := L) s s') {q : U64} :
    IdleAt (L := L) s' q ↔ IdleAt (L := L) s q := by
  unfold IdleAt; rw [hidl.1, hidl.2]

/-- The untyped caps after a step are old ones with the same region and
device flag. -/
def UtFrom (G G' : MdbGhost) (m m' : U64 → U64) : Prop :=
  ∀ x ∈ G'.chains.flatten, ∀ p sb fi d, capV m' x = .Untyped p sb fi d →
    ∃ y ∈ G.chains.flatten, ∃ fi', capV m y = .Untyped p sb fi' d

/-- **`IdleOut` across a step** keeping the idle word, the heaps, and the
untyped regions (each after an old one). -/
theorem IdleOut.keep {th : TypedHeap} {H : Heap} {G G' : MdbGhost} {s s' : S}
    (h : IdleOut (L := L) th H G s) (hidl : IdleKeep (L := L) s s') (hut : UtFrom G G' (L.mem s) (L.mem s')) :
    IdleOut (L := L) th H G' s' := by
  intro x hx p sb fi hc q hq
  obtain ⟨y, hy, fi', hc'⟩ := hut x hx p sb fi false hc
  exact h y hy p sb fi' hc' q ((idleAt_of hidl).1 hq)

/-- **The RAM untyped regions miss the kernel-state block, every core's
node, and the VSpace ASID-table area `[ksb+288000, ksb+288000+16384)`**
(l4v `valid_global_refs` for untyped caps, as `IdleOut`: the kernel
window/globals lie in no untyped region; all three are statics of the
kernel image). The third part (KENTRY-PLAN g5a) asks the whole static area
after the kernel-state base, `[ksb+13568, ksb+288000+16384)`: the 64
cores' node slots (`layout::ks::NODES`, statically allocated whatever the
number of cores, so also the nodes of cores outside `Cs`) and the ASID
table; with the first part, the region misses `[ksb, ksb+304384)`. It gives
`UtNodesJ` (formerly the entry premise `JEntryAt.utks`, `utNodesJ_of_ks`).
Not asked of device untypeds: since losfair/FL4#34 a device
untyped's pointer `paddr + PPTR_BASE` may lie in the kernel image, where
the kernel-state block, the nodes and the ASID table are. -/
def UtKsApart (G : MdbGhost) (Cs : Set U64) (s : S) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV (L.mem s) x = .Untyped p sb fi false →
    (p.val + 2 ^ sb.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val) ∧
    (∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val) ∧
    (p.val + 2 ^ sb.val ≤ (L.ksb s).val + 13568 ∨ (L.ksb s).val + 288000 + 16384 ≤ p.val)

/-- `UtKsApart`'s third part in its former shape (the ASID-table area only). -/
theorem UtKsApart.asidOf {kb p sb : U64}
    (h : p.val + 2 ^ sb.val ≤ kb.val + 13568 ∨ kb.val + 288000 + 16384 ≤ p.val) :
    p.val + 2 ^ sb.val ≤ kb.val + 288000 ∨ kb.val + 288000 + 16384 ≤ p.val := by omega

/-- **`UtKsApart` across a step** keeping the kernel-state base and the
untyped regions (each after an old one, same device flag). -/
theorem UtKsApart.keep {G G' : MdbGhost} {Cs : Set U64} {s s' : S} (h : UtKsApart (L := L) G Cs s)
    (hks : L.ksb s' = L.ksb s) (hut : UtFrom G G' (L.mem s) (L.mem s')) : UtKsApart (L := L) G' Cs s' := by
  intro x hx p sb fi hc
  obtain ⟨y, hy, fi', hc'⟩ := hut x hx p sb fi false hc
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨h1, h2, h3⟩ := h y hy p sb fi' hc'
  exact ⟨by rw [hks]; exact h1, fun c hc => by rw [hnb]; exact h2 c hc, by rw [hks]; exact h3⟩

/-- **Every object is covered by a cap, or is exempt** (`ExAt`: an idle
object, `IdleAt`, or one inside the kernel-state block, `KsObj`), the idle objects outside the RAM untyped regions, and the RAM untyped caps
miss the kernel-state block and the core nodes (module docstring). -/
structure JCov (thp : TypedHeap) (H : Heap) (G : MdbGhost) (Cs : Set U64) (s : S) : Prop where
  th : ∀ q k, thp q = some k → Covered (L.mem s) G q.val (q.val + max (objSize k) 1) ∨ ExAt (L := L) thp H s q
  h : ∀ q k, H q = some k → Covered (L.mem s) G q.val (q.val + 2 ^ k.bits) ∨ ExAt (L := L) thp H s q
  ks : UtKsApart (L := L) G Cs s
  idleOut : IdleOut (L := L) thp H G s

variable {th : TypedHeap} {H : Heap} {G : MdbGhost} {Cs : Set U64} {s : S}

/-- **No object of `th` in a childless untyped region**, so `restrictTh` to
outside it is `th` (MpPlacedHyp's (b)). -/
theorem restrictTh_childless (hJ : JCov (L := L) th H G Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hnd : ∀ y, ¬ Mdb.Desc G.par y x) :
    restrictTh th p.val (p.val + 2 ^ sb.val) = th := by
  funext q
  unfold restrictTh
  split
  · rename_i hq
    cases hk : th q with
    | none => rfl
    | some k =>
      rcases hJ.th q k hk with hc | hi | hi
      · have := ut_free hU hI hx hcx hnd (by omega) hc
        omega
      · have := (hJ.idleOut x hx p sb fi hcx q hi).2.1 k hk
        omega
      · obtain ⟨k1, k2⟩ := hi.1 k hk
        have := (hJ.ks x hx p sb fi hcx).1
        omega
  · rfl

/-- A covered byte is outside a childless untyped region. -/
theorem notin_childless (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64} {d : Bool}
    (hcx : capV (L.mem s) x = .Untyped p sb fi d) (hnd : ∀ y, ¬ Mdb.Desc G.par y x) {lo hi a : Nat}
    (hc : Covered (L.mem s) G lo hi) (h1 : lo ≤ a) (h2 : a < hi) : a < p.val ∨ p.val + 2 ^ sb.val ≤ a := by
  have := ut_free hU hI hx hcx hnd (by omega) hc
  omega

/-- **No `OObj` word in a childless untyped region** (MpPlacedHyp's (a),
`RegOKTop`'s third part), for the other subsystems' sets drawn from `H`,
the IPC-buffer words covered. -/
theorem oobj_childless (hJ : JCov (L := L) th H G Cs s) {Tr C0 : Set U64} {σ : Fl4Spec.State Unit}
    (hP : JPlaced (L := L) th H Tr C0 s σ) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hnd : ∀ y, ¬ Mdb.Desc G.par y x)
    {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} (hc : c ∈ Cs)
    (hT : ∀ t ∈ T, H t = some .tcb) (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply)
    (hN : ∀ n ∈ N, H n = some .ntfn) (hC : ∀ q ∈ C, q ≠ 0#u64)
    (hB : ∀ wp ∈ B, Covered (L.mem s) G wp.1.val (wp.1.val + 8)) :
    ∀ a : U64, p.val ≤ a.val → a.val < p.val + 2 ^ sb.val → ¬ Vs.OObj st N T C E R B c s σ a := by
  intro a h1 h2 hO
  have nin : ∀ {lo hi : Nat}, Covered (L.mem s) G lo hi → lo ≤ a.val → a.val < hi → False :=
    fun hcv l1 l2 => by have := notin_childless hU hI hx hcx hnd hcv l1 l2; omega
  have hks := hJ.ks x hx p sb fi hcx
  have hobj : ∀ {q : U64} {k : HKind}, H q = some k → q.val ≤ a.val → a.val < q.val + 2 ^ k.bits → False :=
    fun {q k} hq l1 l2 => by
      rcases hJ.h q k hq with hcv | hi | hi
      · exact nin hcv l1 l2
      · have := (hJ.idleOut x hx p sb fi hcx q hi).2.2 k hq
        omega
      · obtain ⟨k1, k2⟩ := hi.2 k hq
        have := hks.1
        omega
  rcases hO with ⟨o1, o2⟩ | ⟨o1, o2⟩ | ⟨t, ht, o1, o2⟩ | ⟨e, he, o1, o2⟩ | ⟨r, hr, o1, o2⟩ | ⟨n, hn, o1, o2⟩ |
      ⟨q, hq, y, n, hk, o1, o2⟩ | ⟨wp, hw, o1, o2⟩
  · have := hks.2.1 c hc; omega
  · have := hks.1; omega
  · exact hobj (hT t ht) (by omega) (by simp only [HKind.bits]; omega)
  · exact hobj (hE e he) (by omega) (by simp only [HKind.bits]; omega)
  · exact hobj (hR r hr) (by omega) (by simp only [HKind.bits]; omega)
  · exact hobj (hN n hn) (by omega) (by simp only [HKind.bits]; omega)
  · exact hobj (hP.sc q y n (hC q hq) hk).2 o1 (by simp only [HKind.bits]; have := Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.le_add_right n Fl4Spec.minSchedContextBits); omega)
  · exact nin (hB wp hw) o1 o2

/-- **`OObj` at an outcome** keeping the kernel-state base and creating no
SC is `OObj` at the entry (so MpPlacedHyp's (a) carries to the outcome). -/
theorem OObj.mono {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s' : S}
    {σ σ' : Fl4Spec.State Unit} (hk : L.ksb s' = L.ksb s)
    (hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n))
    {a : U64} (h : Vs.OObj st N T C E R B c s' σ' a) : Vs.OObj st N T C E R B c s σ a := by
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  rcases h with h | h | h | h | h | h | ⟨q, hq, y, n, hky, ho⟩ | h
  · exact Or.inl (by rw [← hnb]; exact h)
  · exact Or.inr (Or.inl (by rw [← hk]; exact h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · obtain ⟨y0, hk0⟩ := hsc q y n hky
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, y0, n, hk0, ho⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem buf_byte {w : Fl4Spec.Word} (hw : w.toNat + 8 ≤ 2 ^ 64) {i : Int} (hi : i ∈ Fl4Spec.intUpto 0 7) :
    w.toNat ≤ (w + (7 - BitVec.ofInt 64 i)).toNat ∧ (w + (7 - BitVec.ofInt 64 i)).toNat < w.toNat + 8 := by
  simp only [Fl4Spec.intUpto, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  have hk' : k < 8 := by omega
  interval_cases k <;> simp [BitVec.toNat_add] <;> omega

/-- **`RegOKTop` at a childless untyped region of 4 KiB** (MakePool's), the
IPC-buffer bytes covered. -/
theorem regOKTop_childless (hJ : JCov (L := L) th H G Cs s) {Tr C0 : Set U64} {σ : Fl4Spec.State Unit}
    (hP : JPlaced (L := L) th H Tr C0 s σ) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hnd : ∀ y, ¬ Mdb.Desc G.par y x) (hsb : sb.val = 12)
    (hpal : p.val % 4096 = 0) (hpf : p.val + 4096 ≤ 2 ^ 64)
    {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} (hc : c ∈ Cs)
    (hT : ∀ t ∈ T, H t = some .tcb) (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply)
    (hN : ∀ n ∈ N, H n = some .ntfn) (hC : ∀ q ∈ C, q ≠ 0#u64)
    (hB : ∀ wp ∈ B, Covered (L.mem s) G wp.1.val (wp.1.val + 8))
    (hB2 : ∀ wp ∈ B, wp.2.toNat + 8 ≤ 2 ^ 64 ∧ Covered (L.mem s) G wp.2.toNat (wp.2.toNat + 8)) :
    Vs.RegOKTop (L := L) N T C E R B c s σ p := by
  have h4 : 2 ^ sb.val = 4096 := by rw [hsb]; rfl
  refine ⟨hpal, hpf, fun a h1 h2 => oobj_childless hJ hP hU hI hx hcx hnd hc hT hE hR hN hC hB a h1 (by omega),
    fun wp hw i hi => ?_⟩
  obtain ⟨hf, hcv⟩ := hB2 wp hw
  obtain ⟨b1, b2⟩ := buf_byte hf hi
  have := notin_childless hU hI hx hcx hnd hcv b1 b2
  omega

/-- **MpPlacedHyp's (a) at the outcome**: no `OObj` word of the outcome
`(s', σ')` in the childless region, when the outcome keeps the kernel-state
base and creates no SC. -/
theorem oobj_out (hJ : JCov (L := L) th H G Cs s) {Tr C0 : Set U64} {σ σ' : Fl4Spec.State Unit} {s' : S}
    (hP : JPlaced (L := L) th H Tr C0 s σ) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hnd : ∀ y, ¬ Mdb.Desc G.par y x)
    {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} (hc : c ∈ Cs)
    (hT : ∀ t ∈ T, H t = some .tcb) (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply)
    (hN : ∀ n ∈ N, H n = some .ntfn) (hC : ∀ q ∈ C, q ≠ 0#u64)
    (hB : ∀ wp ∈ B, Covered (L.mem s) G wp.1.val (wp.1.val + 8))
    (hk : L.ksb s' = L.ksb s)
    (hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n)) :
    ∀ a : U64, p.val ≤ a.val → a.val < p.val + 2 ^ sb.val → ¬ Vs.OObj st N T C E R B c s' σ' a :=
  fun a h1 h2 hO => oobj_childless hJ hP hU hI hx hcx hnd hc hT hE hR hN hC hB a h1 h2 (OObj.mono hk hsc hO)

end

end

end Fl4Proofs.P3.Sched
