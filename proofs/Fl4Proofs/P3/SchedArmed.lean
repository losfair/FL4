/-
P3 (DESIGN.md §9), scheduler relation: **writing a node's `ARMED` word**
(l4h 0006: the deadline the hardware timer is armed for) keeps `SchedRel`
with the spec state unchanged: no part of the relation reads node offset 80.
`SchedRel`'s agreement records (`SAgree`, `CAgree`) ask the word to agree,
so the agreement lemmas are redone here with offset 80 exempt.
-/
import Fl4Proofs.P3.ScFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **The `ARMED` word** (module docstring). -/
theorem SchedRel.set_armed {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (v : U64) :
    SchedRel st N T C c (L.wr s (L.nodeAt s c layout.node.ARMED) v) σ ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (L.nodeAt s c layout.node.ARMED) v)) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have h80 : layout.node.ARMED.val = 80 := by simp [layout.node.ARMED]
  have hA : Aligned (L.nodeAt s c layout.node.ARMED) := nodeAt_aligned hN (by omega) (by omega)
  set s' := L.wr s (L.nodeAt s c layout.node.ARMED) v
  have hk : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 80 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro o ho h8 hne
    refine rd_wr_ne hA (nodeAt_aligned hN ho h8) fun e => hne ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), nodeAt_val hN ho] at this; omega
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 80 → nodeW st s' c o = nodeW st s c o := by
    intro o ho h8 h; unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk]; exact hn o ho h8 h
  have htf : ∀ y ∈ T, ∀ K, SchedField K →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK
    obtain ⟨h1, h2, -⟩ := schedField_ok hK
    exact rd_wr_ne hA (field_aligned (hc.tcbs y hy) h1 h2) (nodeAt_ne_tfield hN (by omega) hy (hc.tcbs y hy) h1)
  have hdom : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := by
    refine rd_wr_ne hA (curDomA_aligned hN) fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), curDomA_val hN] at this
    simp only [LawfulStore.nodeBase] at this; omega
  have hdt : L.mem s' (dtA st s) = L.mem s (dtA st s) := by
    refine rd_wr_ne hA (dtA_aligned hN) fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), dtA_val hN] at this
    have h2 := hN.fits
    simp only [LawfulStore.nodeBase] at this h2; omega
  have hscw : ∀ sc ∈ C, ScAgree st s s' sc := by
    intro sc hsc a hal hin
    refine rd_wr_ne hA hal fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega)] at this
    have := (hS.scOutIn hsc hin).2.1; omega
  -- the TCB fields
  have haff : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y) := fun y hy => htf y hy _ (by simp [SchedField])
  have hpr : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) := fun y hy => htf y hy _ (by simp [SchedField])
  have hdm : ∀ y ∈ T, L.mem s' (domA y) = L.mem s (domA y) := fun y hy => htf y hy _ (by simp [SchedField])
  have hsw : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => htf y hy _ (by simp [SchedField])
  have hiq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => htf y hy _ (by simp [SchedField])
  have hnx : ∀ y ∈ T, L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) := fun y hy =>
    htf y hy _ (by simp [SchedField, nextOff])
  have hpv : ∀ y ∈ T, L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y) := fun y hy =>
    htf y hy _ (by simp [SchedField, prevOff])
  have hlinks : ∀ {q xs}, QueueRel (L.mem s) T .Sched q xs → QueueRel (L.mem s') T .Sched q xs :=
    fun hq => ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨hpv y (hq.mem y hy), hnx y (hq.mem y hy)⟩⟩
  -- the core's queues
  have hv : ViewsEq st s s' c := by
    refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
    · simp only [LawfulStore.rqQ, nodeAt_ksb hk]
      rw [hn _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega),
        hn _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)]
    · simp only [LawfulStore.l1W, nodeAt_ksb hk]
      exact hn _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega)
    · simp only [LawfulStore.l2W, nodeAt_ksb hk]
      exact hn _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
  have hrel : L.relQ s' c = L.relQ s c := by
    simp only [LawfulStore.relQ, nodeAt_ksb hk]
    rw [hn _ (by rw [relh_val]; omega) (by rw [relh_val]) (by rw [relh_val]; omega),
      hn _ (by rw [relt_val]; omega) (by rw [relt_val]) (by rw [relt_val]; omega)]
  have hc' : SchedCore st T c s' Q R := by
    refine ⟨hc.tcbs, nodePlaced_ksb hc.node hk, (L.cpu_wr _ _ _).trans hc.cur,
      fun t ht => (haff t ht).trans (hc.aff t ht),
      fun t ht => (hpr t ht) ▸ hc.prio t ht,
      ⟨hc.ready.1.agree hv.1 fun p hp y hy =>
        ⟨hnx y ((hc.ready.1.rel p hp).mem y hy), hpv y ((hc.ready.1.rel p hp).mem y hy)⟩, hc.ready.2.views hv⟩,
      hrel ▸ hlinks hc.release,
      fun p hp t ht => (hpr t ((hc.ready.1.rel p hp).mem t ht)).trans (hc.inQ p hp t ht),
      fun t ht => by rw [hiq t ht, hpr t ht]; exact hc.queued t ht,
      fun t ht => by rw [hiq t ht]; exact hc.released t ht,
      fun t ht => by rw [hpr t ht]; exact hc.excl t ht, ?_, ?_, by rw [hk]; exact hc.ksOut⟩
    · rw [nw _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]
      exact hc.curT
    · rw [nw _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]
      exact hc.idleT
  have hs' : SchedSpec st T C c s' Q R σ := by
    refine ⟨hs.rq, hs.rqDom, hs.rel, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_, fun t ht => ?_, fun sc hsc => ?_,
      by rw [nw _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]
         exact hs.idleSc,
      by rw [dtA_ksb hk, hdt]; exact hs.domTime,
      by rw [nw layout.node.IDLE_THREAD (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
           (by simp [layout.node.IDLE_THREAD])]
         exact hs.idleTh⟩
    · rw [nw _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]
      exact hs.curThread
    · rw [nw _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]
      exact hs.curSc
    · rw [nw _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]
      exact hs.curTime
    · rw [nw _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])]
      exact hs.consumed
    · rw [curDomA_ksb hk, hdom]; exact hs.curDom
    · obtain ⟨x, hkx, h1, h2, h3, h4⟩ := hs.tcb t ht
      exact ⟨x, hkx, h1, by rw [hdm t ht]; exact h2, by rw [hsw t ht]; exact h3, by rw [hpr t ht]; exact h4⟩
    · rw [hsw t ht]; exact hs.scMem t ht
    · obtain ⟨x, n, hkx, e⟩ := hs.scs sc hsc
      exact ⟨x, n, hkx, e.agree (hscw sc hsc)⟩
  refine ⟨⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, by rw [dtA_ksb hk]; exact hS.dtNW,
    scOut_transfer hk (SzKeep.of_kheap rfl) hS.scOut, scDisj_transfer (SzKeep.of_kheap rfl) hS.scDisj,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.act,
    by rw [nw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      (by simp [layout.node.REPROGRAM])]; exact hS.repr,
    hs.core_eq hscw hS.core, Q, R, hc', hs'⟩, node_wr_foot hS (by omega) (by omega)⟩

end

end

end Fl4Proofs.P3.Sched
