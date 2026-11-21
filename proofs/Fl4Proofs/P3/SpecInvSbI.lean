/-
P3 (DESIGN.md §9), invariant line G1 (sb1): **the `SIK` (ScInv-kept) family's
leaves and `si_auto`** (spec side only; imports SpecInvSbP). Leaves: every `SBK`
frame (`sik_of_sbk` + `sb_leaf`) and the hand-proved writers
(`sik_schedContextUnbindTcb`, `sik_maybeReturnSc`, `sik_schedContextSetInactive`,
`sik_replyPush`, `sik_replyRemove`, `sik_maybeDonateSc`, `sik_sendIpc`).
-/
import Fl4Proofs.P3.SpecInvSbP
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

syntax "si_leaf" : tactic
macro_rules | `(tactic| si_leaf) => `(tactic| fail "no si_leaf")

macro "si_auto" : tactic => `(tactic| repeat' (first | si_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| si_leaf) => `(tactic| ((with_reducible refine sik_of_sbk (fun _ => ?_)); sb_leaf))
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact sik_schedContextUnbindTcb _)
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact sik_maybeReturnSc _ _)
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact sik_schedContextSetInactive _)
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact sik_replyPush _ _ _ _)
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact sik_replyRemove _ _)
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact sik_maybeDonateSc _ _)
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact sik_sendIpc _ _ _ _ _ _ _ _)

end Fl4Proofs.P3.SInvB
