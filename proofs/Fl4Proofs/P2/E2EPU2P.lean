/-
# P2 (line p2P, gen 1): the [P] audit of `serializable_fl4_localU1` — `serializable_fl4_localU2`

Every [P] of `serializable_fl4_localU1` (P2/E2EPU2.lean and the start facts it builds on) checked against the Rust
(`crates/fl4-sync/src/lib.rs`, `crates/fl4-store/src/lock.rs`, `crates/fl4-kernel`, `crates/fl4-core`); the full
table with evidence is in the line's handoff. Classes: (a) derivable — proved here and removed;
(b) kept, a faithful statement of fl4-sync / entry / hardware behaviour; (c) false somewhere it is required.

## (a) — removed in `serializable_fl4_localU2`
* `hm : MasksWr st` — **`masksWr_plain`**: from `[PlainStore st]` (masks are the constant `(0, 0)`), which the top
  already assumes. `hSt : StoreTotal st` — `LawfulStore.total`.
* `kd` of every W11 record (vmF `VmFPremB`, vmR `VmRPremA`, io `IoPremW9`, st `StPremW3B`, irq `IrqPremK2B`, vx
  `VxPremP3E`, vt `VtPremA0`, sl `SlPremP6`) and `lk` of the invocation records (`DelPtePrem`, `InvPremW` for
  CNodeDelete and Copy / Mint): all hold for a **constant** lock map (`LkC.kernDetS`, `LkC.kernDetAt`, `LkC.wr`).
  The constant map is the faithful one: fl4-sync takes every lock before the body (`lock_object`, `with_locks`,
  `lookup_slot_locked`) and releases them only after it (`unlock_held`); the extracted body takes none. So **`LkC`**
  (the index's `Locks` is `fun _ => X`) is an untagged index convention, like `ix`; `StartAt`'s `Locks σ = hs` then
  makes `X` exactly the held set. The sat lemmas' `planLocks p` is such a map (`lkC_planLocks`).
* `cs` of vmR / sl (`∀ c ∈ Cs, c.val < 64`): from the entry's bundle (`BunIxU.ac` / `SlEntU.ix`, `SlJAtZ.csLt`).
  vmR's / sl's records are no longer asserted: `nv` from the epoch, `bun` from the chain, `cs`, `kd` as above.

## (b) — kept (each checked; details in the handoff)
`LocPlat`, `MRKeepIoapic`, `ArchTotal` (P3 / Arch); `SerExitW`, `serG`, `MapsP` (ghost choices); `arm` (fl4-sync
writes nothing before the body); `GlueAt`; `NonIdle` (entries from user mode, idle runs only in `fl4_idle`); vmF
`lk` / `gl`, vmR `lk` / `nbc`, sl `el` / `hlk` / `nbc` / `acc` / `sc.arm` (fl4-sync's locks and checks, verbatim);
vmR `fd` / sl `sc.fd` (`reply_caps` at the start state: fl4-sync evaluates it before locking, it holds at the start
because no word it reads is an empty or frame-cap slot, the only slot words written beside the gate); st `fd`
(`lookup_slot_locked` = `resolve_address_bits` level by level); irq `lt`, `pl`; vx `hv`, `buf` (vacuous: no VCPU).

## (c) — reported, not changed
1. Local paths with no slot: X86Page_Map (`local_invocation`), `local_vm_syscall`, `local_vm_entry`, guest VM exits:
   at their `start` no index's start fact holds, so `Fl4StepWPR.start` is false for any run that uses them.
2. `vcpus = ∅` at every exit and record: only VCPU-free runs are covered.
3. The x86 page walkers' A/D-bit writes of PTEs and paging-structure entries (kernel words) are no model step
   (`HwStepP` is vacuous at `vcpus = ∅`), so `GlueAt`'s memory clause fails at a real start after such a write.
   No wrong behaviour found (the paths read address / present bits only).
No lock-map premise is false: fl4-store's 4,096-entry hash only coarsens the model's per-address locks.

## Theorems
`masksWr_plain`, `LkC` (+ `.kernDetS`, `.kernDetAt`, `.wr`, `lkC_const`, `lkC_planLocks`), `StartU2`, `InvLkW`,
`StartInvU3`, `StartV2`, **`startU_of_U2`**, **`serializable_fl4_localU2`** (U1's premises minus `hm`, `hSt`,
`kd` ×8, `cs` ×2, `lk` ×3; plus the convention `LkC`); no vacuity: `startU2_of_U`, `startInvU3_of_U2` (U2's start
facts from U1's at a constant lock map, so every U1 satisfiability lemma applies). No new [W] / [J] / [P].
New module; no existing statement changes.

**Collapse A, Q:** the top `serializable_fl4_localU2` is removed (it had no user but jboot's `Fl4ProofsQ` copy of
P2/WitExec's `wit_U2_io`; the B3-deferred non-vacuity witnesses went with it). The start facts above stay: U3 / U4
use them.
-/
import Fl4Proofs.P2.E2EPU2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## `MasksWr` and `StoreTotal` from the store classes -/

section store
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **`MasksWr` holds of every `PlainStore`** (its masks are the constant `(0, 0)`): the top's `hm` [P] is
derivable from the `[PlainStore st]` instance the top already assumes. -/
theorem masksWr_plain [Fl4Proofs.P1.PlainStore st] : E2E.MasksWr st :=
  fun s a v => by rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]

end store

/-! ## A constant lock map -/

section lk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The glue's lock map is constant** (index convention, untagged; module docstring): the index's `Locks` is the
set of objects fl4-sync holds, which it takes before the body (`with_locks`, `lock_object`) and releases only after
it (`unlock_held`); the extracted body takes no lock. -/
def LkC (Locks : S → U64 → Prop) : Prop := ∃ X : U64 → Prop, Locks = fun _ => X

theorem LkC.kernDetS {Locks : S → U64 → Prop} (h : LkC Locks) (U : Set U64) (s : S) :
    KernDetS (L := L) U Locks s := by
  obtain ⟨X, rfl⟩ := h
  exact fun _ _ _ _ _ => rfl

theorem LkC.kernDetAt {Locks : S → U64 → Prop} (h : LkC Locks) (K : KLayout) (s : S) :
    KernDetAt (L := L) K Locks s := by
  obtain ⟨X, rfl⟩ := h
  exact fun _ _ _ _ _ => rfl

theorem LkC.wr {Locks : S → U64 → Prop} (h : LkC Locks) (s : S) (b v : U64) : Locks (L.wr s b v) = Locks s := by
  obtain ⟨X, rfl⟩ := h
  rfl

theorem lkC_const (X : U64 → Prop) : LkC (fun _ : S => X) := ⟨X, rfl⟩

end lk

/-! ## The start facts without `kd` / `cs` / `lk` -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The eight W11 slots' start facts without `kd` / `cs`** (module docstring): `StartU` (at `hm` / `hSt` from the
store classes) with every record's `kd` [P] replaced by `LkC` of the index's lock map (`kd` stated as the hypothesis
it now is), and vmR's / sl's records (`cs` [P], `kd` [P]) no longer asserted: the record is built from the entry's
bundle (`cs`), `LkC` (`kd`), the epoch's `K.vcpus = ∅` and the chain (`nv`, `bun`). -/
def StartU2 (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => LkC j.Locks ∧ ((∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.Locks s) →
      StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch K m hK hU c hs q (.vmF j))
  | .vmR j => ∃ q0, (LkC j.Locks ∧ ∃ σ : S, (Ch σ ∧ VmREntU st arI AR MR j (userV K.toKLayoutV) K.toKLayout σ) ∧
      ∀ h : VmRPremA st j K.toKLayoutV,
        GlueAt ((vmRSlotA st ar hA (masksWr_plain st)).liftAt j K.toKLayoutV m hK.base hU.base h)
          (fun σ' : S => σ' = σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | .sl j => ∃ q0, (LkC j.Locks ∧ ∃ σ : S, (Ch σ ∧ SlEntU st ar arI AR MR j K.toKLayoutV.toKLayout σ) ∧
      ∀ h : (slSlotP3W6 st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV m,
        GlueAt ((slSlotP3W6 st ar hA (masksWr_plain st) L.total a0).liftAt j K.toKLayoutV m hK.base hU.base h)
          (fun σ' : S => σ' = σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | .io j => LkC j.Locks ∧ ((∀ s, SlJAt (L := L) K.toKLayoutV.toKLayout s →
        KernDetS (L := L) (userV K.toKLayoutV).user j.Locks s) →
      StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch K m hK hU c hs q (.io j))
  | .st j => LkC j.lk ∧ ((∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.lk s) →
      StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch K m hK hU c hs q (.st j))
  | .irq j => LkC j.lk ∧ ((∀ s, SlJAt (L := L) K.toKLayoutV.toKLayout s →
        KernDetS (L := L) (userV K.toKLayoutV).user j.lk s) →
      StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch K m hK hU c hs q (.irq j))
  | .vq (.inl j) => LkC j.lk ∧ ((∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.lk s) →
      StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch K m hK hU c hs q (.vq (.inl j)))
  | .vq (.inr j) => LkC j.lk ∧ ((∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.lk s) →
      StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch K m hK hU c hs q (.vq (.inr j)))

/-- The invocation slots' lock premise (`InvPremW.lk` / `DelPtePrem.lk`), as a formula. -/
def InvLkW (Locks : S → U64 → Prop) : Prop :=
  ∀ (K' : OwnMap.KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
    Locks (L.wr s b v) = Locks s

/-- **The three invocation summands' start facts without `lk`**: `StartInvU2` (at `hm` from `PlainStore`) with
`InvPremW.lk` / `DelPtePrem.lk` [P] replaced by `LkC` of the index's lock map. -/
def StartInvU3 (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : (InvArg S ⊕ InvArg S) ⊕ InvArg S → Prop
  | .inl (.inl j) => LkC j.Locks ∧ (InvLkW st j.Locks →
      DelPteStart st ar hA (masksWr_plain st) Ch K m hK hU c hs q j)
  | .inl (.inr j) => LkC j.Locks ∧ (InvLkW st j.Locks →
      InvStartU2 st ar hA (masksWr_plain st) Ch K m hK hU c hs q j)
  | .inr j => LkC j.Locks ∧ (InvLkW st j.Locks →
      CMStartU2 st ar hA (masksWr_plain st) Ch K m hK hU c hs q j)

/-- **The start facts of U2's family**: `StartU2` on the eight W11 slots, `StartInvU3` on the invocation summands. -/
def StartV2 (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S) → Prop
  | .inl i => StartU2 st ar hA a0 arI AR MR Ch K m hK hU c hs q i
  | .inr j => StartInvU3 st ar hA Ch K m hK hU c hs q j

variable {arI AR MR}

/-- **`StartU2` gives `StartU`** at a layout with no VCPU whose chain is `Ch`. -/
theorem startU_of_U2 {Ch : S → Prop} {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (nv : K.vcpus = ∅) {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartU2 st ar hA a0 arI AR MR Ch K m hK hU c hs q i) :
    StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch K m hK hU c hs q i := by
  obtain ⟨σe, hC'⟩ := hC
  cases i with
  | vmF j => exact h.2 (fun s => h.1.kernDetS _ s)
  | vmR j =>
    obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, hG⟩, e⟩ := h
    obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, B, -⟩ := hE.ix.ac
    have hR : VmRPremA st j K.toKLayoutV :=
      ⟨nv, ⟨σ, by rw [userV_empty nv]; exact ChainOf.bun hC' σ hCσ⟩, B.csLt, fun s _ => hL.kernDetAt _ s⟩
    exact ⟨q0, ⟨hR, (hG hR).mono fun σ' e' _ => by rw [e']; exact ⟨hCσ, hE⟩⟩, e⟩
  | sl j =>
    obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, hG⟩, e⟩ := h
    obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, B, -⟩ := hE.ix
    have hR : (slSlotP3W6 st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV m :=
      show K.toKLayoutV.vcpus = ∅ ∧ SlPremP6 st j K.toKLayoutV from
        ⟨nv, ⟨σ, ChainOf.bun hC' σ hCσ⟩, B.csLt, fun K' s _ => hL.kernDetAt K' s⟩
    exact ⟨q0, ⟨hR, (hG hR).mono fun σ' e' _ => by rw [e']; exact ⟨hCσ, hE⟩⟩, e⟩
  | io j => exact h.2 (fun s _ => h.1.kernDetS _ s)
  | st j => exact h.2 (fun s => h.1.kernDetS _ s)
  | irq j => exact h.2 (fun s _ => h.1.kernDetS _ s)
  | vq j =>
    rcases j with j | j
    · exact h.2 (fun s => h.1.kernDetS _ s)
    · exact h.2 (fun s => h.1.kernDetS _ s)

/-- **No vacuity: `StartU2` holds wherever `StartU` does with a constant lock map** (so every satisfiability lemma
of U1 — `startU_vmF_sat`, `startU_vmR_sat`, `startU_sl_sat`, `startU_vt_sat`, PJ12's — gives one of U2 at an index
whose `Locks` is `fun _ => X`, where `kd` holds by `LkC`). -/
theorem startU2_of_U {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (hL : LkC (match i with
      | .vmF j => j.Locks | .vmR j => j.Locks | .io j => j.Locks | .st j => j.lk | .irq j => j.lk
      | .sl j => j.Locks | .vq (.inl j) => j.lk | .vq (.inr j) => j.lk))
    (h : StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch K m hK hU c hs q i) :
    StartU2 st ar hA a0 arI AR MR Ch K m hK hU c hs q i := by
  cases i with
  | vmF j => exact ⟨hL, fun _ => h⟩
  | vmR j =>
    obtain ⟨q0, ⟨_, σ, a, ⟨hCσ, hE⟩, hc, hl, hμ, e0⟩, e⟩ := h
    exact ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, fun _ => ⟨σ, a, rfl, hc, hl, hμ, e0⟩⟩, e⟩
  | sl j =>
    obtain ⟨q0, ⟨_, σ, a, ⟨hCσ, hE⟩, hc, hl, hμ, e0⟩, e⟩ := h
    exact ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, fun _ => ⟨σ, a, rfl, hc, hl, hμ, e0⟩⟩, e⟩
  | io j => exact ⟨hL, fun _ => h⟩
  | st j => exact ⟨hL, fun _ => h⟩
  | irq j => exact ⟨hL, fun _ => h⟩
  | vq j =>
    rcases j with j | j
    · exact ⟨hL, fun _ => h⟩
    · exact ⟨hL, fun _ => h⟩

/-- `StartInvU3` holds wherever `StartInvU2` does with a constant lock map (e.g. `planLocks p`, the lock map of
`invStartU2_sat` / `cmStartU2_sat` / `startU1_delPte_sat`). -/
theorem startInvU3_of_U2 {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    {c : U64} {hs : U64 → Prop} {q : SP} {j : (InvArg S ⊕ InvArg S) ⊕ InvArg S}
    (hL : LkC (match j with | .inl (.inl j) => j.Locks | .inl (.inr j) => j.Locks | .inr j => j.Locks))
    (h : StartInvU2 st ar hA (masksWr_plain st) Ch K m hK hU c hs q j) :
    StartInvU3 st ar hA Ch K m hK hU c hs q j := by
  rcases j with (j | j) | j
  · exact ⟨hL, fun _ => h⟩
  · exact ⟨hL, fun _ => h⟩
  · exact ⟨hL, fun _ => h⟩

/-- `planLocks p` is constant. -/
theorem lkC_planLocks (p : localinv.Plan) : LkC (planLocks (S := S) p) :=
  ⟨fun x => ∃ i : Nat, i < p.n.val ∧ p.locks.val[i]? = some x, rfl⟩

end start

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}


end top

end
end Fl4Proofs.P2.E2EP
