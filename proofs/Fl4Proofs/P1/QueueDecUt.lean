/-
P1: InvGaps' `untyped` family down to the retype: `untyped.decode`
(Untyped_Retype) is error leaves with the state unchanged up to the caller's
restart, then `untyped.retype`; the retype after the restart (the reset and
the object creation, which may grow the heap) is the named premise
`UtPlace.retype`, in `Cur0` form, with the decode's checks as its
hypotheses (`UtArgs`).
-/
import Fl4Proofs.P1.QueueDecVs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- What the decode has checked before a retype of the untyped cap
`Untyped ptr sb fi dev` (at `slot`), from the state `s0` it started in: the
object size `val` (below 64), the destination CNode `dest` and its empty
window `[off, off + win)` (from the CNode cap at the extra slot `x`), the
reset (no children), the aligned base from the free index, the window fits
the free bytes, and a device untyped makes only frames or untypeds. -/
def UtArgs (st : machine.Store S) [L : LawfulStore st] (s0 : S) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slot ptr sb fi : U64) (dev reset : Bool) (aligned nt us dest off win : U64) : Prop :=
  ∃ x ∈ extra.val, x ≠ 0#u64 ∧ ∃ idx dep val : U64,
    untyped.retype_size nt us = ok (.Ok val) ∧ val.val < 64 ∧
    untyped.retype_dest st s0 x idx dep off win = ok (.Ok dest) ∧
    untyped.ensure_empty_slots st s0 dest off (core.num.U64.wrapping_add off win) = ok (.Ok ()) ∧
    (reset = true ↔ ∃ v, cdt.ensure_no_children st s0 slot = ok (.Ok v)) ∧
    untyped.align_up (core.num.U64.wrapping_add ptr (if reset then 0#u64 else fi)) val = ok aligned ∧
    (∃ i2 i4, (1#u64 <<< (sb &&& 63#u64) : Result U64) = ok i2 ∧
      (core.num.U64.wrapping_sub i2 (if reset then 0#u64 else fi) >>> (val &&& 63#u64) : Result U64) = ok i4 ∧
      win.val ≤ i4.val) ∧
    (dev = true → objects.is_frame_type nt = ok true ∨ nt = fl4_abi.consts.object.Untyped)

/-- P3's fact at every untyped decode's start (`UtOk s slot cap extra`, of
the state, the invoked slot (holding the cap), its untyped cap and the extra caps, e.g. l4v's
`valid_untyped` of the joint state and the per-cap facts): what the retype's
P3 facts rest on. -/
def UtOkAt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop)
    (UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop) : Prop :=
  ∀ (Ac : Set U64) (s : S) (slot ptr sb fi : U64) (dev : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Untyped ptr sb fi dev) extra → CapSlotW T Ω Sg slot →
      obj.Slot.cap st slot s = ok (.Untyped ptr sb fi dev) → UtOk s slot (.Untyped ptr sb fi dev) extra

/-- The queue and heap placement obligation of the shared-frame extension.
It is only reachable on stores that advertise guest memory sharing. -/
def SharedUtPlace (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64)
    (UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop) : Prop :=
  ∀ {Ac : Set U64} {s : S} (a : A) (len slot buf ptr sb fi : U64) (dev : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize), machine.sharing_enabled st s = ok true →
    UtOk s slot (.Untyped ptr sb fi dev) extra →
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Untyped ptr sb fi dev) extra → CapSlotW T Ω Sg slot →
    untyped.retype_shared st ar s a len slot (.Untyped ptr sb fi dev) buf extra ⦃ r s' _ =>
      DecPostG st Adm Cs Ac s r s' ⦄

/-- **The untyped family's retype, the named premise**: after the caller's
restart (`Cur0` from the decode's start `s0`), the retype the decode
checked (`UtArgs`) ends over some admissible set tuple (`DecPostG`: the
heap may grow). -/
structure UtPlace (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64)
    (UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop) : Prop where
  shared : SharedUtPlace st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk
  retype : ∀ (Ac : Set U64) (s0 s : S) (a : A) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slot ptr sb fi : U64) (dev reset : Bool) (aligned nt us dest off win : U64),
    UtOk s0 slot (.Untyped ptr sb fi dev) extra →
    sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s →
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s0 (.Untyped ptr sb fi dev) extra → CapSlotW T Ω Sg slot →
    UtArgs st s0 extra slot ptr sb fi dev reset aligned nt us dest off win →
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
    untyped.retype st ar s a slot reset aligned nt us dest off win dev ⦃ r s' _ =>
      DecPostG st Adm Cs Ac s0 r s' ⦄

theorem shr_and63 (x y : U64) : (x >>> (y &&& 63#u64) : Result U64) ⦃ _ => True ⦄ := by
  p0_auto

set_option hygiene false in
/-- An error leaf with the state unchanged (a growing-heap post). -/
local macro "errU" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (DecPost.toG' hσ D (D.err _))
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg]
     exact (WP.spec_ok _).2 (DecPost.toG' hσ D (D.err _))))

/-- A fixed-heap post from a `DecPre` state is a growing-heap one. -/
theorem DecPost.toG' {Adm : PSets → Prop} {s s' : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {r : core.result.Result Unit error.Exc}
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (h : DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s') : DecPostG st Adm Cs Ac s r s' :=
  ⟨_, hσ, D.bxi.1.choose_spec.choose_spec.curT, h⟩


set_option hygiene false in
/-- The aligned base, the restart and the retype premise. -/
local macro "utalign" dv:term : tactic => `(tactic| (
  obtain ⟨al, eal, -⟩ := spec_exists' (P0.untyped.align_up.p0 _ val)
  rw [eal]
  simp only [bind_ok]
  refine WP.spec_bind (spec_eqv (Cur0.restart D)) fun s2 ⟨erst, h2⟩ => ?_
  exact Pl.retype Ac s s2 a extra slot ptr sb fi dev _ al nt us dest off win hOk erst D hslot
    ⟨x, hxm, hx0, idx, dep, val, ers, hv64, erd, ere,
      (by first
        | exact ⟨(fun _ => ⟨_, ern⟩), (fun _ => rfl)⟩
        | exact ⟨(fun h => by cases h), (fun ⟨v, hv⟩ => by rw [ern] at hv; simp at hv)⟩),
      by simpa using eal, ⟨i2, i4, e2, by simpa using e4, Nat.le_of_not_lt fun h => hwin h⟩, $dv⟩ h2))

set_option hygiene false in
/-- The decode's tail, from the object size. -/
local macro "uttail" : tactic => `(tactic| (
  obtain ⟨rs, ers, -⟩ := spec_exists' (P0.untyped.retype_size.p0 nt us)
  rw [ers]
  simp only [bind_ok]
  rcases rs with val | e
  swap
  · errU
  simp only [irq_branch_ok, bind_ok]
  obtain ⟨rd, erd, -⟩ := spec_exists' (P0.untyped.retype_dest.p0 st s x idx dep off win hS)
  rw [erd]
  simp only [bind_ok]
  rcases rd with dest | e
  swap
  · errU
  simp only [irq_branch_ok, bind_ok, lift]
  obtain ⟨re, ere, -⟩ := spec_exists' (P0.untyped.ensure_empty_slots.p0 st s dest off
    (core.num.U64.wrapping_add off win) hS)
  rw [ere]
  simp only [bind_ok]
  rcases re with u0 | e
  swap
  · errU
  simp only [irq_branch_ok, bind_ok, untyped.as_untyped]
  obtain ⟨rn, ern, -⟩ := spec_exists' (P0.cdt.ensure_no_children.p0 st s slot hS)
  rw [ern]
  simp only [bind_ok]
  rcases rn with v | e
  all_goals
    simp only [bind_ok, uncurry_apply_pair, lift]
    obtain ⟨i2, e2, -⟩ := spec_exists' (shl_and63 sb)
    rw [e2]
    simp only [bind_ok, lift]
    obtain ⟨i4, e4, -⟩ := spec_exists' (shr_and63 _ val)
    rw [e4]
    simp only [bind_ok]
    split
    · errU
    rename_i hwin
    split
    · errU
    rename_i h64
    have hv64 : val.val < 64 := by scalar_tac
    split
    · obtain ⟨bf, ebf, -⟩ := spec_exists' (P0.objects.is_frame_type.p0 nt)
      rw [ebf]
      simp only [bind_ok]
      split
      · rename_i hbf
        utalign (fun _ => Or.inl (by rw [ebf, hbf]))
      · split
        · errU
        · rename_i hnu
          utalign (fun _ => Or.inr (UScalar.eq_of_val_eq (by simpa [fl4_abi.consts.object.Untyped] using hnu)))
    · rename_i hnd
      utalign (fun h => absurd h hnd)))

set_option maxHeartbeats 16000000 in
/-- **`untyped.decode`** (Untyped_Retype) down to the retype (`UtPlace`). -/
theorem untyped.decode.dec {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop}
    (Pl : UtPlace st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk)
    {s : S} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len slot buf ptr sb fi : U64) (dev : Bool)
    (hOk : UtOk s slot (.Untyped ptr sb fi dev) extra)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Untyped ptr sb fi dev) extra) (hslot : CapSlotW T Ω Sg slot) :
    untyped.decode st ar s a lbl len slot (.Untyped ptr sb fi dev) buf extra ⦃ r s' _ =>
      DecPostG st Adm Cs Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold untyped.decode
  by_cases c1 : (lbl != fl4_abi.label.UntypedRetype) = true
  · rw [if_pos c1]
    split
    · obtain ⟨b, hb, -⟩ := spec_exists' (P0.machine.sharing_enabled.p0 st s hS)
      rw [hb]
      cases b
      · simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]; errU
      · simpa only [bind_ok, ↓reduceIte] using Pl.shared a len slot buf ptr sb fi dev extra hb hOk D hslot
    · errU
  rw [if_neg c1]
  by_cases c2 : len < 6#u64
  · rw [if_pos c2]; errU
  rw [if_neg c2]
  refine WP.spec_bind (idx_mem extra 0#usize (by simp)) fun x hxm => ?_
  simp only [obj.Slot.is_null, bind_ok]
  by_cases c3 : decide (x = 0#u64) = true
  · rw [if_pos c3]; errU
  rw [if_neg c3]
  have hx0 : x ≠ 0#u64 := by simpa using c3
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun nt _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun us _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun off _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun win _ => ?_
  by_cases c4 : nt >= fl4_abi.consts.object.X86Vcpu
  · rw [if_pos c4]
    by_cases c5 : nt < fl4_abi.consts.object.Count
    · rw [if_pos c5]
      refine WP.spec_bind (hA.virtualization a) fun i _ => ?_
      by_cases c6 : i = 0#u64
      · rw [if_pos c6]; errU
      rw [if_neg c6]
      uttail
    · rw [if_neg c5]
      uttail
  · rw [if_neg c4]
    uttail

/-- **InvGaps' `untyped`, discharged** down to the retype premise
`UtPlace`, over a growing heap. -/
theorem decGap_untyped {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop}
    (Pl : UtPlace st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk) (hOk : UtOkAt st T Cs Ω H Sg Rp Scs Nt Z U P3Ok UtOk) :
    DecGapG st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok .untyped := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot hcs hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact untyped.decode.dec hA hσ Pl a lbl len slot buf _ _ _ _ (hOk _ _ _ _ _ _ _ _ hE D hslot hcs) D hslot

end

end Fl4Proofs.P1
