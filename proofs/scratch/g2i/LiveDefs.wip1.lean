/-
P3 (DESIGN.md §9), CSpace: **the definitions of the liveness bundle `LiveDN`**
(KENTRY-PLAN g2i), moved upstream of `JointAt` so that `JAtZ` can carry it as a
field (`JAtZ.live`, with `JAtZ.zD`: the TCB zombies' TCBs in the dead set).

* `RefsObj`, `InUse`, `dbgNth`, `KsSlot`, `dbgHead`, `LiveJ` (from
  XTopJointLive; its module docstring explains them);
* `nextIn`, `prevA`, `DbgWFL`, `DbgWF`, `DbgWFL.congr`, `dbgHd`, `DbgWFs`,
  `dbgHd_of_ksb` (from DbgWF);
* `NullOrig`, `NullOrig.notInUse`, `NullOrig.of_same`, `orig_eq_of_slots`
  (from XTopJointNullOrig);
* `dbgNth_keep`, `LiveJ.of_same`, `ZTcb`, `LiveJ.ztcb`, `LiveJ.of_sameZ`,
  `DbgWFL.of_keep` (from XTopJointLiveKeep);
* `LiveDN` (from XTopJointWJLRestart).
Statements and proofs unchanged (names fully qualified where the new opens
would be ambiguous).
-/
import Fl4Proofs.P3.XTopCnodeAll
import Fl4Proofs.P3.XTopTcbAll
import Fl4Proofs.P3.IpcSendDon
import Fl4Proofs.P3.ScXProd
import Fl4Proofs.P3.ScUtRetype
import Fl4Proofs.P3.ScIpcSorted
import Fl4Proofs.P3.ScRecvLinks
import Fl4Proofs.P3.VsCapW
import Fl4Proofs.P3.BufDefs
import Fl4Proofs.P1.QueueDbgKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- The cap names the CNode or TCB `q` as a container (module docstring). -/
def RefsObj (q : U64) : capability.Cap → Prop
  | .CNode p _ _ _ => p = q
  | .Thread p => p = q
  | .Zombie p _ _ => p = q
  | _ => False

/-- The slot `y` holds a cap or an original bit. -/
def InUse (m : U64 → U64) (σ : Fl4Spec.State Unit) (y : U64) : Prop :=
  capV m y ≠ .Null ∨ ∃ x, cslotAddr x = y ∧ σ.isOriginalCap x = true

/-- The `n`-th TCB of the debug list from `h` (`0` past its end). -/
def dbgNth (m : U64 → U64) : Nat → U64 → U64
  | 0, h => h
  | n + 1, h => if h = 0#u64 then 0#u64 else dbgNth m n (m (P1.dnA h))

/-- The successor of `x` in `l` (`0` past the end or if absent). -/
def nextIn : List U64 → U64 → U64
  | [], _ => 0#u64
  | a :: r, x => if a = x then r.headD 0#u64 else nextIn r x

/-- The predecessor of `x` in `l`, `q` before the first. -/
def prevA : U64 → List U64 → U64 → U64
  | _, [], _ => 0#u64
  | q, a :: r, x => if a = x then q else prevA a r x

/-- **The debug lists' shape** (module docstring), with the lists given. -/
structure DbgWFL (T Cs : Set U64) (m : U64 → U64) (hd : U64 → U64) (lst : U64 → List U64) : Prop where
  head : ∀ c ∈ Cs, m (hd c) = (lst c).headD 0#u64
  next : ∀ c ∈ Cs, ∀ x ∈ lst c, m (P1.dnA x) = nextIn (lst c) x
  prev : ∀ c ∈ Cs, ∀ x ∈ lst c, m (P1.dpA x) = prevA 0#u64 (lst c) x
  nodup : ∀ c ∈ Cs, (lst c).Nodup
  zero : ∀ c ∈ Cs, 0#u64 ∉ lst c
  mem : ∀ c ∈ Cs, ∀ x ∈ lst c, x ∈ T ∧ m (P1.affA x) = c
  off : ∀ y ∈ T, (∀ c ∈ Cs, y ∉ lst c) → m (P1.dnA y) = 0#u64 ∧ m (P1.dpA y) = 0#u64

/-- **The debug lists are well formed** [J] (module docstring). -/
def DbgWF (T Cs : Set U64) (m : U64 → U64) (hd : U64 → U64) : Prop := ∃ lst, DbgWFL T Cs m hd lst

/-- `DbgWFL` reads the TCBs' debug and affinity words and the cores' head
words only. -/
theorem DbgWFL.congr {T Cs : Set U64} {m m' hd hd' : U64 → U64} {lst : U64 → List U64} (h : DbgWFL T Cs m hd lst)
    (hy : ∀ y ∈ T, m' (P1.dnA y) = m (P1.dnA y) ∧ m' (P1.dpA y) = m (P1.dpA y) ∧ m' (P1.affA y) = m (P1.affA y))
    (hh : ∀ c ∈ Cs, m' (hd' c) = m (hd c)) : DbgWFL T Cs m' hd' lst :=
  ⟨fun c hc => (hh c hc).trans (h.head c hc),
    fun c hc x hx => ((hy x (h.mem c hc x hx).1).1).trans (h.next c hc x hx),
    fun c hc x hx => ((hy x (h.mem c hc x hx).1).2.1).trans (h.prev c hc x hx),
    h.nodup, h.zero,
    fun c hc x hx => ⟨(h.mem c hc x hx).1, ((hy x (h.mem c hc x hx).1).2.2).trans (h.mem c hc x hx).2⟩,
    fun y hyT hn => ⟨((hy y hyT).1).trans (h.off y hyT hn).1, ((hy y hyT).2.1).trans (h.off y hyT hn).2⟩⟩

/-- **The debug list walked over kept links** (module docstring). -/
theorem dbgNth_keep {T : Set U64} {m m' : U64 → U64} (hdn : ∀ y ∈ T, m' (P1.dnA y) = m (P1.dnA y))
    (hcl : ∀ y ∈ T, P1.Tz T (m (P1.dnA y))) : ∀ (n : Nat) (h : U64), P1.Tz T h → dbgNth m' n h = dbgNth m n h := by
  intro n
  induction n with
  | zero => intro h _; rfl
  | succ n ih =>
    intro h hh
    simp only [dbgNth]
    by_cases h0 : h = 0#u64
    · simp [h0]
    · have hT : h ∈ T := hh.ne0 h0
      simp only [h0, ↓reduceIte]
      rw [hdn h hT]
      exact ih _ (hcl h hT)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A slot inside the kernel-state block** `[kb, kb + 13568)` (the IRQ
node's one-slot CNodes, `IntLayout.node`; `SlotLiveAt`'s right disjunct). -/
abbrev KsSlot (kb y : U64) : Prop := kb.val ≤ y.val ∧ y.val < kb.val + 13568

/-- Core 0's debug-list head. -/
abbrev dbgHead (s : S) : U64 := L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)

/-- **The liveness invariant of FL4's caps** [J] (module docstring). -/
structure LiveJ (th : TypedHeap) (H : P1.Heap) (G : MdbGhost) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  slots : ∀ q i, IsSlotAt th q i → InUse (L.mem s) σ (slotOf q i) →
    (∃ y ∈ G.chains.flatten, RefsObj q (capV (L.mem s) y)) ∨ KsSlot (L.ksb s) (slotOf q i)
  dbg : ∀ n, dbgNth (L.mem s) n (dbgHead (L := L) s) ≠ 0#u64 →
    (dbgNth (L.mem s) n (dbgHead (L := L) s)).bv ≠ σ.idleThread →
    ∃ y ∈ G.chains.flatten, capV (L.mem s) y = .Thread (dbgNth (L.mem s) n (dbgHead (L := L) s))
  zslots : ∀ y, IsSlot th y → ∀ p zt n, capV (L.mem s) y = .Zombie p zt n →
    ∀ i, IsSlotAt th p i → n.val ≤ i → ¬ InUse (L.mem s) σ (slotOf p i)
  zdead : ∀ y, IsSlot th y → ∀ p zt n, capV (L.mem s) y = .Zombie p zt n → zt.val = 65 →
    DeadP (L := L) H s p

/-- The cores' debug-list head words. -/
abbrev dbgHd (s : S) : U64 → U64 := fun c => L.nodeAt s c layout.node.DEBUG_TCBS

/-- **The debug lists of a state are well formed** [J] (module docstring). -/
abbrev DbgWFs (T Cs : Set U64) (s : S) : Prop := DbgWF T Cs (L.mem s) (dbgHd (L := L) s)

theorem dbgHd_of_ksb {s s' : S} (h : L.ksb s' = L.ksb s) : dbgHd (L := L) s' = dbgHd (L := L) s := by
  funext c; unfold dbgHd P1.LawfulStore.nodeAt; rw [h]

/-- **A null abstract slot is not original** [J] (module docstring). -/
def NullOrig (th : TypedHeap) (m : U64 → U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ sl, AbsSlot th sl → capV m (cslotAddr sl) = .Null → σ.isOriginalCap sl = false

/-- **A null slot is not in use.** -/
theorem NullOrig.notInUse {th : TypedHeap} {m : U64 → U64} {σ : Fl4Spec.State Unit} (hN : NullOrig th m σ)
    (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl) {y : U64} (hy : capV m y = .Null) :
    ¬ InUse m σ y := by
  rintro (h | ⟨x, rfl, hx⟩)
  · exact h hy
  · rw [hN x (horig x hx) hy] at hx; cases hx

/-- **`NullOrig` across a step keeping the slots' caps and the original bits.** -/
theorem NullOrig.of_same {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (hN : NullOrig th m σ)
    (hcv : ∀ y, IsSlot th y → capV m' y = capV m y) (ho : σ'.isOriginalCap = σ.isOriginalCap) :
    NullOrig th m' σ' := fun sl hA h => by
  rw [ho]; exact hN sl hA (by rw [← hcv _ hA.isSlot]; exact h)

/-- **The original bits kept by a step keeping the slots' words** (`CdtRel`
before and after, the bits only on abstract slots). -/
theorem orig_eq_of_slots {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G G' : MdbGhost}
    (hC : CdtRel th m σ G) (hC' : CdtRel th m' σ' G') (ho : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (ho' : ∀ sl, σ'.isOriginalCap sl = true → AbsSlot th sl) (hS : SlotsSame th m m') :
    σ'.isOriginalCap = σ.isOriginalCap := by
  funext sl
  by_cases hA : AbsSlot th sl
  · rw [hC'.orig sl hA, hC.orig sl hA, hS.revOf hA.isSlot]
  · cases h1 : σ'.isOriginalCap sl
    · cases h2 : σ.isOriginalCap sl
      · rfl
      · exact absurd (ho sl h2) hA
    · exact absurd (ho' sl h1) hA

/-- **`LiveJ` across a step keeping the slots** (module docstring). -/
theorem LiveJ.of_same {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {Cs : Set U64} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (hL : LiveJ (L := L) th H G s σ) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hmem : ∀ y ∈ G.chains.flatten, IsSlot th y) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hid : σ'.idleThread = σ.idleThread)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hc0 : 0#u64 ∈ Cs) (hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s)
    (hdead : ∀ p, DeadP (L := L) H s p → DeadP (L := L) H s' p) :
    LiveJ (L := L) th H G s' σ' := by
  have hU : ∀ y, IsSlot th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hu => by
    unfold InUse at hu ⊢
    rw [hSS.capV hy, horig] at hu
    exact hu
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hK.1]
    exact hK.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hN : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') = dbgNth (L.mem s) n (dbgHead (L := L) s) := fun n => by
    rw [hhd]
    exact dbgNth_keep (fun y hy => hK.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) n _ (hTz.dh _ hc0)
  refine ⟨fun q i hqi hu => ?_, fun n hn hni => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
    fun y hy p zt n hz hzt => ?_⟩
  · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hu) with ⟨y, hy, hr⟩ | hb
    · exact Or.inl ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
    · exact Or.inr (by rw [hK.1]; exact hb)
  · rw [hN] at hn hni ⊢
    obtain ⟨y, hy, hr⟩ := hL.dbg n hn (by rw [← hid]; exact hni)
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
  · exact hL.zslots y hy p zt n (by rw [← hSS.capV hy]; exact hz) i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hu)
  · exact hdead p (hL.zdead y hy p zt n (by rw [← hSS.capV hy]; exact hz) hzt)

/-- The TCBs of the TCB zombies (type 65) in the slots. -/
def ZTcb (th : TypedHeap) (s : S) : Set U64 :=
  {p | ∃ y, IsSlot th y ∧ ∃ zt n, capV (L.mem s) y = .Zombie p zt n ∧ zt.val = 65}

/-- `LiveJ.zdead` on `ZTcb`. -/
theorem LiveJ.ztcb {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hL : LiveJ (L := L) th H G s σ) : ∀ p ∈ ZTcb (L := L) th s, DeadP (L := L) H s p :=
  fun _ ⟨y, hy, zt, n, hz, h65⟩ => hL.zdead y hy _ zt n hz h65

/-- **`LiveJ.of_same` with only the TCB zombies' TCBs dead after** (`ZTcb`). -/
theorem LiveJ.of_sameZ {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {Cs : Set U64} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (hL : LiveJ (L := L) th H G s σ) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hmem : ∀ y ∈ G.chains.flatten, IsSlot th y) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hid : σ'.idleThread = σ.idleThread)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hc0 : 0#u64 ∈ Cs) (hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s)
    (hdead : ∀ p ∈ ZTcb (L := L) th s, DeadP (L := L) H s' p) :
    LiveJ (L := L) th H G s' σ' := by
  have hU : ∀ y, IsSlot th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hu => by
    unfold InUse at hu ⊢
    rw [hSS.capV hy, horig] at hu
    exact hu
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hK.1]
    exact hK.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hN : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') = dbgNth (L.mem s) n (dbgHead (L := L) s) := fun n => by
    rw [hhd]
    exact dbgNth_keep (fun y hy => hK.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) n _ (hTz.dh _ hc0)
  refine ⟨fun q i hqi hu => ?_, fun n hn hni => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
    fun y hy p zt n hz hzt => ?_⟩
  · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hu) with ⟨y, hy, hr⟩ | hb
    · exact Or.inl ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
    · exact Or.inr (by rw [hK.1]; exact hb)
  · rw [hN] at hn hni ⊢
    obtain ⟨y, hy, hr⟩ := hL.dbg n hn (by rw [← hid]; exact hni)
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
  · exact hL.zslots y hy p zt n (by rw [← hSS.capV hy]; exact hz) i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hu)
  · exact hdead p ⟨y, hy, zt, n, by rw [← hSS.capV hy]; exact hz, hzt⟩

/-- **`DbgWFL` across a step keeping the debug words and the affinities.** -/
theorem DbgWFL.of_keep {T Cs : Set U64} {s s' : S} {lst : U64 → List U64}
    (hW : DbgWFL T Cs (L.mem s) (dbgHd (L := L) s) lst) (hK : P1.DbgKeep st T Cs s s')
    (haff : ∀ y ∈ T, L.mem s' (P1.affA y) = L.mem s (P1.affA y)) :
    DbgWFL T Cs (L.mem s') (dbgHd (L := L) s') lst :=
  hW.congr (fun y hy => ⟨hK.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩), hK.2 _ (Or.inl ⟨y, hy, Or.inr rfl⟩), haff y hy⟩)
    (fun c hc => by rw [dbgHd_of_ksb hK.1]; exact hK.2 _ (Or.inr ⟨c, hc, rfl⟩))

/-- **`LiveJ`, `DbgWF` and `NullOrig` at a state** (module docstring). -/
abbrev LiveDN (th : TypedHeap) (H : P1.Heap) (Cs : Set U64) (G : MdbGhost) (s : S) (σ : Fl4Spec.State Unit) :
    Prop :=
  LiveJ (L := L) th H G s σ ∧ DbgWF (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s) ∧ NullOrig th (L.mem s) σ

end

end

end Fl4Proofs.P3
