/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
guest page tables** (proofs/VIRT-PLAN.md §6).

One guest-physical page-table spec for Intel EPT and AMD nested paging
(FL4 `ept.rs`: "On AMD the same objects contain nested page tables"), in
the shape of the ported x64 VSpace (`X64/VSpace`): four levels of 512
entries, the tables `.archObj (.ept level entries)` of the ported heap
(levels 0 = root, 39 = PDPT, 30 = PD, 21 = PT; FL4's `Cap::Ept.level`), a
root reachable through its guest-tagged ASID pool entry (`r ||| 1`,
`asidEntryRoot`, `nativeAsidRoot` = none).

Entries are the ported shape's words. `GuestPte` is their abstract
meaning and `GuestPte.encode` FL4's encoding per backend (`ept.rs`
`frame_entry`, the table entry `paddr | 7`); `GuestPte.decode` reads a
word as the hardware does on both backends: present/readable bit 0,
writable bit 1, large page bit 7, address bits 51:12 (SDM Vol. 3C
§29.3.2 Tables 29-1..29-6; APM Vol. 2 §15.25.5 with the long-mode PTE
format of §5.3). Execute is always granted (EPT bit 2; NPT has no NX
bit set). The memory type is EPT bits 5:3 or NPT's PAT index (PWT, PCD,
PAT bits); the guest's PAT still applies (no EPT IPAT bit).

The x86 geometry is fixed (4 levels, 48-bit GPA, FL4 maps below 2^47);
`GuestGeom` is the parameter AArch64 Stage-2 will instantiate (3- or 4-level
walks, concatenated roots; upstream `arch/aarch64/ept.rs`), not specified
here.

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtState

namespace Fl4Spec

noncomputable section
open Classical

/-- A guest page-table geometry: the shifts of the levels from the root
down to the smallest page (x86: 39, 30, 21, 12) and the GPA limit. -/
structure GuestGeom where
  shifts : List Nat
  gpaLimit : Word

/-- FL4's x86 geometry (`ept.rs`: `LIMIT` = 2^47, `lookup`'s shifts). -/
def x86GuestGeom : GuestGeom := ⟨[39, 30, 21, 12], 1 <<< 47⟩

/-- FL4 `ept.rs` `ADDRESS`: entry address bits 51:12. -/
def guestPteAddress : Word := 0x000f_ffff_ffff_f000

/-- FL4 `ept::memory_type`: UC (0), WC (1), WT (4) and WB (6) as asked,
anything else WB (SDM Vol. 3C §29.3.7). WP (5) is not passed through
(VIRT-PLAN.md FINDING V5). -/
def guestMemoryType (attr : Word) : Word :=
  if attr = 0 ∨ attr = 1 ∨ attr = 4 ∨ attr = 6 then attr else 6

/-- The meaning of a guest page-table entry. -/
inductive GuestPte where
  | invalid
  /-- the next-level table at physical address `paddr` -/
  | table (paddr : Paddr)
  /-- a frame at `paddr`; `large` at a non-leaf level (2 MiB in FL4),
  `write` its write right (read and execute always), `memType` the
  EPT memory type (`guestMemoryType`) -/
  | frame (paddr : Paddr) (large : Bool) (write : Bool) (memType : Word)
deriving Inhabited

/-- FL4's NPT PAT index for an EPT memory type (`ept::frame_entry`: UC 3,
WC 4, WT 1, WP 5, WB 0, the native fixed PAT palette). -/
def npTPatIndex (mt : Word) : Word :=
  if mt = 0 then 3 else if mt = 1 then 4 else if mt = 4 then 1 else if mt = 5 then 5 else 0

/-- FL4's encoding (`ept::frame_entry`, `ept::decode` map: `paddr | 7`).
`invalid` is 0. -/
def GuestPte.encode (k : VirtKind) : GuestPte → Word
  | .invalid => 0
  | .table p => p ||| 7
  | .frame p large write mt =>
    let w : Word := if write then 2 else 0
    let ps : Word := if large then 128 else 0
    if k = .svm then
      let pat := npTPatIndex mt
      let cache := ((pat &&& 1) <<< 3) ||| ((pat &&& 2) <<< 3) |||
        ((pat &&& 4) <<< (if large then 10 else 5))
      p ||| 1 ||| w ||| 4 ||| ps ||| cache
    else p ||| 1 ||| w ||| 4 ||| ps ||| (mt <<< 3)

/-- The hardware's reading of an entry at a level with `shift` (module
docstring): not present; a frame at the last level or with bit 7; a
table otherwise. The memory type is not decoded (it does not affect
what the guest can reach). -/
def GuestPte.decode (shift : Nat) (e : Word) : GuestPte :=
  if e &&& 1 = 0 then .invalid
  else if shift = 12 ∨ e &&& 128 ≠ 0 then .frame (e &&& guestPteAddress) (shift ≠ 12) (e &&& 2 ≠ 0) 0
  else .table (e &&& guestPteAddress)

/-- The entry index of `gpa` at a level (`ept::lookup`). -/
def guestIndex (gpa : Word) (shift : Nat) : BitVec 9 := BitVec.ofNat 9 ((gpa >>> shift).toNat % 512)

/-- The entries of the guest table at `p` in the heap, if it is one. -/
def guestTableAt (h : KHeap) (p : ObjRef) : Option (BitVec 9 → Word) :=
  match h p with
  | some (.archObj (.ept _ es)) => some es
  | _ => none

/-- The hardware walk of a guest-physical address from table `p` through
the levels `shifts`: the frame it reaches (physical address of the
frame's base, its size in bits, write right), or none. -/
def guestWalk (h : KHeap) : ObjRef → List Nat → Word → Option (Paddr × Nat × Bool)
  | _, [], _ => none
  | p, s :: rest, gpa =>
    match guestTableAt h p with
    | none => none
    | some es =>
      match GuestPte.decode s (es (guestIndex gpa s)) with
      | .invalid => none
      | .frame pa _ w _ => some (pa &&& ~~~(((1 : Word) <<< s) - 1), s, w)
      | .table pa => guestWalk h (ptrFromPAddr pa) rest gpa

/-- The guest root a thread runs on (FL4 `kernel/entry.rs` `exit`, the
TCB's EPT slot through `ept::root`): its `tcbEpt` cap is a mapped level-0
EPT cap whose ASID's pool entry is that root, guest-tagged. Otherwise the
thread runs on FL4's empty root (`vm::empty_root`): `none`, no frame
reachable. -/
def guestRootOf {Z : Type} (σ : State Z) (t : ObjRef) : Option ObjRef :=
  match σ.kheap t with
  | some (.tcb tcb) =>
    match tcb.tcbEpt with
    | .archObjectCap (.eptCap r 0 (some (a, _))) =>
      match σ.archState.x64AsidTable (asidHighBitsOf a) with
      | none => none
      | some p => match σ.kheap p with
        | some (.archObj (.asidPool f)) =>
          match f (asidLowBitsOf a) with
          | some e => if e &&& 1 = 1 ∧ asidEntryRoot e = r ∧ a ≠ 0 then some r else none
          | none => none
        | _ => none
    | _ => none
  | _ => none

/-- A byte of kernel memory (the ported `underlyingMemory`, indexed by
kernel address) that the guest of root `r` can write: inside a frame
mapped writable at some GPA below the limit. -/
def GuestWritableByte {Z : Type} (σ : State Z) (r : Option ObjRef) (a : Word) : Prop :=
  ∃ root gpa pa sz, r = some root ∧ gpa < x86GuestGeom.gpaLimit ∧
    guestWalk σ.kheap root x86GuestGeom.shifts gpa = some (pa, sz, true) ∧
    pa ≤ addrFromPPtr a ∧ addrFromPPtr a - pa < (1 : Word) <<< sz

/-- A byte the guest of root `r` can read (any mapped frame). -/
def GuestReadableByte {Z : Type} (σ : State Z) (r : Option ObjRef) (a : Word) : Prop :=
  ∃ root gpa pa sz w, r = some root ∧ gpa < x86GuestGeom.gpaLimit ∧
    guestWalk σ.kheap root x86GuestGeom.shifts gpa = some (pa, sz, w) ∧
    pa ≤ addrFromPPtr a ∧ addrFromPPtr a - pa < (1 : Word) <<< sz

end

end Fl4Spec
