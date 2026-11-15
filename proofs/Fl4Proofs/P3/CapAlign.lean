/-
P3 (DESIGN.md §9), CSpace: **frame caps are aligned** (l4v `cap_aligned`,
part of `CapValid`): a frame cap in a slot of the typed heap names a frame
aligned to its size.
-/
import Fl4Proofs.P3.CnodeCopy
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

theorem CapValid.frame_align {th : TypedHeap} {p : U64} {sz : capability.FrameSize} {r : U64} {d m : Bool}
    {a va : U64} (h : CapValid th (.Frame p sz r d m false a va)) : p.val % 2 ^ frameBitsN sz = 0 := h

/-- A large frame cap's frame is 2 MiB aligned. -/
theorem CapValid.frame_large {th : TypedHeap} {p : U64} {r : U64} {d m : Bool} {a va : U64}
    (h : CapValid th (.Frame p .Large r d m false a va)) : p.val % 2 ^ 21 = 0 := h

/-- **The frame cap in a slot of a CNode or TCB is aligned.** -/
theorem frame_aligned_of_slot {th : TypedHeap} {mem : U64 → U64} (hV : SlotsValid th mem) {sl : Fl4Spec.CslotPtr}
    (h : AbsSlot th sl) {p : U64} {sz : capability.FrameSize} {r : U64} {d m : Bool} {a va : U64}
    (hc : capAt mem (cslotAddr sl) = ok (.Frame p sz r d m false a va)) : p.val % 2 ^ frameBitsN sz = 0 :=
  (hV.abs h hc).frame_align

/-- **A 4 KiB alias of a page of an aligned frame is aligned**: for the
caps DeriveSubframe inserts (the frame at `q`, `q = p + o` with `o` a
multiple of 4 KiB, `p` the large frame's base). -/
theorem CapValid.small_of_large {th : TypedHeap} {p q : U64} {o : Nat} {r r' : U64} {d d' m m' : Bool}
    {a a' va va' : U64} (h : CapValid th (.Frame p .Large r d m false a va)) (ho : o % 4096 = 0)
    (hq : q.val = p.val + o) : CapValid th (.Frame q .Small r' d' m' false a' va') := by
  show q.val % 2 ^ 12 = 0
  have h21 : p.val % 2 ^ 21 = 0 := h
  rw [hq]; omega

end Fl4Proofs.P3
