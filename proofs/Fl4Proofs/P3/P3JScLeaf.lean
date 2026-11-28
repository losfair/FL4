/-
P3 (p3J gen 38): **the SchedContext cap's decode leaf at the dispatch state for every label but Unbind / YieldTo,
for both classes** (one leaf, generic in the flags).

* `decScOtherJSt`: ScJointYield's `decode_invocation_sched_context_otherJ` (a label of no SC invocation: both
  decodes fail, the state unchanged) with `J.stab` for `JAt`.
* **`decScSt`** (any `blk` / `call` / `don` / `fp`): at a dispatch state (`Entered`), for a SchedContext cap whose
  label is neither `SchedContextUnbind` nor `SchedContextYieldTo`, `XCapP` at `MidX` / `MidXP`: the X is
  P3JScFt's `decScJ3St` (Consumed / Bind / UnbindObject: ScJointStep's route, its premises from the dispatch
  state — the SC's facts `JAtZ.scCtxCap`, the caller schedulable `ct_schedulable`, `ScStepP1` by ScRestJ's
  `JAtZ.scCtxStepP1`, the arch relation by KEntryU30's `decode_sched_context_keepAR` with `ARIface`'s `ARKeep`,
  the reply `sc_consumedReplyJSt`) or `decScOtherJSt`; the footprint P3JScFt's `scDecFootJ` (`XCap.andW`); `MR`
  by `XCapP.mrT` (a SchedContext cap is `QuietF`); never preempted (`specDec_noPreK`). Platform facts:
  `TimeAgree` (`min_budget`), `getMaxTicksToUs`, `ticks_to_us` (the tops' `hT`, `hmax`, `htu`).
No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JScFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 38) **The SchedContext cap with a label of no SC invocation, `XCap` at stable ghosts**
(ScJointYield's `decode_invocation_sched_context_otherJ`, the same proof with `J.stab` for `JAt`). -/
theorem decScOtherJSt (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    (l44 : lbl ≠ fl4_abi.label.SchedContextConsumed) (l41 : lbl ≠ fl4_abi.label.SchedContextBind)
    (l43 : lbl ≠ fl4_abi.label.SchedContextUnbindObject) (l42 : lbl ≠ fl4_abi.label.SchedContextUnbind)
    (l45 : lbl ≠ fl4_abi.label.SchedContextYieldTo)
    {sc : U64} (sb : U64) (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 → L.mem s (scW sc 24#u64) ∈ Z.T)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JStab (L := L) arI AR Z H Cs) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  left
  have hS := J.xtop.fin.1.1.1
  have h44 : lbl.val ≠ 44 := fun h => l44 (UScalar.eq_of_val_eq (by simp [h]))
  have h41 : lbl.val ≠ 41 := fun h => l41 (UScalar.eq_of_val_eq (by simp [h]))
  have h43 : lbl.val ≠ 43 := fun h => l43 (UScalar.eq_of_val_eq (by simp [h]))
  have h42 : lbl.val ≠ 42 := fun h => l42 (UScalar.eq_of_val_eq (by simp [h]))
  have h45 : lbl.val ≠ 45 := fun h => l45 (UScalar.eq_of_val_eq (by simp [h]))
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; unfold scLabelOf; simp [h41, h42, h43, h44, h45]
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  swap
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, J.stab⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold schedcontext.decode
  step with P1.obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq] at hi
  subst hi
  refine WP.spec_bind (show _ ⦃ r => r = (s, a) ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = false := by simp [h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]; exact (WP.spec_ok _).mpr rfl
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = true := by simp [h0]
      simp only [this, ↓reduceIte]; exact remote_tcb_stall_id (ar := arI) a hS (hback h0)
  intro r hr
  subst hr
  show (sched.cur_thread st s >>= _) ⦃ _ ⦄
  rw [hct, bind_tc_ok]
  rw [ite_eq_right l44, ite_eq_right l41, ite_eq_right l43, ite_eq_right l42, ite_eq_right l45]
  refine illegal_ok s a _ (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err ?_, Or.inl trivial⟩,
    J.stab⟩)
  unfold Fl4Spec.decodeSchedContextInvocation; rw [hg]; rfl

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **The SchedContext cap's decode at a dispatch state, any flags, any label but Unbind /
YieldTo** (module docstring). -/
theorem decScSt (hA : P0.ArchTotal arI) (hARI : ARIface arI AR) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.SchedContext p sb))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hu : info.label ≠ fl4_abi.label.SchedContextUnbind) (hy : info.label ≠ fl4_abi.label.SchedContextYieldTo)
    (args : List Fl4Spec.Data) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.SchedContext p sb) bl call don fp buf e mi.miLabel
      args ci sl exs buffer ct := by
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  have hq : QuietF (.SchedContext p sb) := by simp [QuietF]
  refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hq hMb (fun _ _ _ h => by cases h))
    (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hq) σb _ hd.1 inv rfl)
  have hX := J.xtop
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  obtain ⟨hpC, hpi, hsb, hssz, hback, hbn⟩ := J.scCtxCap arI hAs.isSlot hc
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  rw [← hLb]
  obtain ⟨sl', hlbl, hsame, hd⟩ := sc_canon info.label
  refine XCapP.lbl_congr arI (specDec_sc p sb hd) ?_
  refine XCap.toPN arI ?_ (specDec_noPreK (by trivial))
  have hex := ExtraOK.rel1 hX.rel.1 (hXO e exs he hexs)
  have hx0 := exAt_idx0 e
  have hxS : exAt e 0 ≠ 0#u64 → IsSlot Z.th (exAt e 0) := fun h => by
    rcases hex with ⟨e0, -⟩ | ⟨-, hs, -⟩
    · exact absurd e0 h
    · exact hs
  obtain ⟨hcur, xc, hkc, hrun⟩ := J.curRunnable hnib hct
  have hcs := ct_schedulable (J.curInv (by rw [hnib.2]; simp)) J.act J.inv (hcur ▸ hkc) hrun
  rw [hcur] at hcs
  refine XCap.andW (X := JStab (L := L) arI AR (Z.mv Z.G V') H Cs)
    (Q := fun s1 => P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ?_
    (scDecFootJ J hT (hT.mb a') hmax (htu a') info.label sl' hlbl sb hpC hpi hback hbn hct hcs e (exAt e 0) hx0
      exs hex (msgLen info buf) (cslotAddr sl) buf bl call don fp)
  by_cases hl : ScJLabel s' info.label p
  · obtain rfl : sl' = info.label.bv := hsame (by rcases hl with h | h | h <;> rw [h] <;> simp)
    exact decScJ3St s' a' σb J hnib.2 hT (hT.mb a') hmax (htu a') Ipc.msgOK_holds info.label info.label.bv hlbl sb
      hpC hpi hl hback hbn hct hcs e (exAt e 0) hx0 exs hex (msgLen info buf) (cslotAddr sl) buf bl call don fp
      args ci sl buffer hc hAs.isSlot hsb hssz hxS
      (decode_sched_context_keepAR L.total hA hARI.toARKeep)
      (WP.spec_mono (JAtZ.scCtxStepP1 hA J hnib hct hAs.isSlot hc hl hex) fun _ h _ _ _ => h)
      (fun l44 => sc_consumedReplyJSt s' a' σb J hnib hA hmax (htu a') info.label info.label.bv hlbl l44 sb hpC
        hback hct e exs (msgLen info buf) (cslotAddr sl) buf bl call don fp)
  · exact decScOtherJSt s' a' σb J info.label sl' hlbl (fun h => hl (Or.inl h)) (fun h => hl (Or.inr (Or.inl h)))
      (fun h => hl (Or.inr (Or.inr h))) hu hy sb (fun h0 => (hback h0).1) hct e exs (msgLen info buf)
      (cslotAddr sl) buf bl call don fp args ci sl buffer

end

end

end Fl4Proofs.P3
