/-
P3 (DESIGN.md §9), CSpace (KENTRY-PLAN g2f (a)): **the deletion's
preempted state keeps `LiveDN`**, so a CNode Delete / Revoke ends with
`LiveDN` on both branches.

* `JAtZ.ppw_tcbWord`, `JAtZ.ppw_nodeWord`: the preemption point's writes
  (P1's `PPW`: `WORK_UNITS` and the current node's `CUR_TIME` / `CONSUMED`)
  miss every TCB word (`ksOut`, `node_ne_field`) and every other word of the
  current node.
* `JAtZ.deadP_ppw`: a dead TCB stays dead across those writes (its state,
  SC, bound notification and yield words, the action and idle words).
* `JAtZ.liveDN_ppw`: `LiveDN` at the preempted state from `LiveDN` before:
  the slots kept (`SlotsSame`), the original bits (`pp_ksm'`, the spec's
  preemption point writes no CDT / original bit), the spec's idle thread
  (`gke_preemptionPoint'`), the debug words (`JAtZ.ppDbg`), the TCB zombies'
  TCBs dead (`deadP_ppw`; a TCB zombie's object is a TCB by `DelInv.zwf`),
  the affinities (`ppw_tcbWord`). No `JAtZ` is needed after (the preempted
  state need not be one: `OffOK` may fail).
* `JAtPreMVL` (`JAtPreMV` with `LiveDN` at the preempted state, at the ghosts
  of the `JAtZ` before the preemption point), `WJPML := WJP ∧ JAtPreMVL ∧
  LiveDN` (XTopJointMRDel's `WJPM` with the liveness),
  `jPreemptHypLML : PPHypDW (WMR MR WJL) WJPML` (XTopJointMRDel's
  `jPreemptHypLM` plus `liveDN_ppw` on the preempted branch).
* `delHypsJLML`, `JDelHypLML`, `JDelParts.jDelHypLML`: the whole deletion of
  one cap at `WJPML` (`DelHypsWRZ`'s `pp` replaced).
* `JAtL` (`JAt` with `LiveDN` at its own ghosts), `cn_del_topJLML`,
  `decode_invocation_cnode_{revoke,delete}JLML`: XTopJointMRCnode's
  `cn_del_topJLM` / `decode_invocation_cnode_{revoke,delete}JLM` with the
  posts `JAtL` / `JAtPreMVL`: `LiveDN` at the outcome on the error, the
  completed and the preempted branch (the error branch and the fast path at
  the entry state, from `hLv`).
-/
import Fl4Proofs.P3.XTopJointMRCnode
import Fl4Proofs.P3.UtResetSpecJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {th : TypedHeap} {Z : XSets}
  {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

/-- **A TCB word is kept by the preemption point's writes** (module docstring). -/
theorem JAtZ.ppw_tcbWord {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hw : P1.WritesIn st s s' (P1.PPW st s))
    {t : U64} (ht : H t = some .tcb) {K : U64} (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := by
  have htT : t ∈ P1.Heap.tcbs H := ht
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hta : P1.TcbAddr t := hq.tcbs t htT
  have hN : P1.NodePlaced st (P1.Heap.tcbs H) s (L.cpu s) := P1.TInv.nodes J.blk _ J.kern.cpuCs
  refine hw.2.2 _ (P1.field_aligned hta hK hK8) fun hb => ?_
  have hv := P1.field_val hta hK
  have e12 : (2 : Nat) ^ 12 = 4096 := rfl
  rcases hb with e | e | e
  · have := congrArg UScalar.val e
    rw [hv, workUnits_val J.kern.ksbFit] at this
    have hko := hq.ksOut t htT
    rw [e12] at hko
    omega
  · exact P1.node_ne_field hN (o := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME]) htT hta hK
      (by unfold P1.LawfulStore.nodeA at e; exact e.symm)
  · exact P1.node_ne_field hN (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED]) htT hta hK
      (by unfold P1.LawfulStore.nodeA at e; exact e.symm)

/-- **A word of the current node other than `CUR_TIME` / `CONSUMED` is kept
by the preemption point's writes.** -/
theorem JAtZ.ppw_nodeWord {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hw : P1.WritesIn st s s' (P1.PPW st s))
    {o : U64} (ho : o.val < 4288) (ho8 : o.val % 8 = 0) (h48 : o.val ≠ 48) (h40 : o.val ≠ 40) :
    L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
  have hN : P1.NodePlaced st (P1.Heap.tcbs H) s (L.cpu s) := P1.TInv.nodes J.blk _ J.kern.cpuCs
  rw [hw.2.1, P1.nodeAt_of_ksb hw.1]
  refine hw.2.2 _ (P1.nodeAt_aligned hN ho ho8) fun hb => ?_
  have hv := P1.nodeAt_val hN ho
  have hnb : L.nodeBase s (L.cpu s) = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 := rfl
  have e48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
  have e40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  rcases hb with e | e | e
  · have := congrArg UScalar.val e
    rw [hv, workUnits_val J.kern.ksbFit, hnb] at this
    omega
  · have := congrArg UScalar.val e
    unfold P1.LawfulStore.nodeA at this
    rw [hv, P1.nodeAt_val hN (by rw [e48]; omega), e48] at this
    omega
  · have := congrArg UScalar.val e
    unfold P1.LawfulStore.nodeA at this
    rw [hv, P1.nodeAt_val hN (by rw [e40]; omega), e40] at this
    omega

/-- **A dead TCB stays dead across the preemption point's writes** (module
docstring). -/
theorem JAtZ.deadP_ppw {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hw : P1.WritesIn st s s' (P1.PPW st s))
    {p : U64} (hp : H p = some .tcb) (hd : DeadP (L := L) H s p) : DeadP (L := L) H s' p := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd.1 hp
  have k : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add p K) = L.mem s (core.num.U64.wrapping_add p K) :=
    fun K hK hK8 => J.ppw_tcbWord arI hw hp hK hK8
  have ea : L.actionW s' = L.actionW s := by
    unfold P1.LawfulStore.actionW
    exact J.ppw_nodeWord arI hw (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
      (by rw [act_val]; omega)
  have ei : L.idleW s' = L.idleW s := by
    unfold P1.LawfulStore.idleW
    exact J.ppw_nodeWord arI hw (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)
      (by rw [idle8]; omega)
  refine ⟨fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun h => by rw [hp] at h; cases h,
    fun h => by rw [hp] at h; cases h, fun h => by rw [hp] at h; cases h, fun z h => by rw [hp] at h; cases h⟩
  · rw [P1.stA_eq] at d1 ⊢; rw [k _ (by simp) (by simp)]; exact d1
  · show L.mem s' (core.num.U64.wrapping_add p 3464#u64) = 0#u64
    rw [k _ (by simp) (by simp)]; exact d2
  · show L.mem s' (core.num.U64.wrapping_add p 3368#u64) = 0#u64
    rw [k _ (by simp) (by simp)]; exact d3
  · rw [ea]; exact d4
  · rw [ei]; exact d5
  · show L.mem s' (core.num.U64.wrapping_add p 3472#u64) = 0#u64
    rw [k _ (by simp) (by simp)]; exact d6

/-- **`LiveDN` at the preempted state** (module docstring). -/
theorem JAtZ.liveDN_ppw {G : MdbGhost} {V : XVs} {s s' : S} {a : A} {σ σ' : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ G)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ) (hw : P1.WritesIn st s s' (P1.PPW st s))
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    {r : Except Unit Unit} (hm : (r, σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) :
    LiveDN (L := L) Z.th H Cs G s' σ' := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := hLv
  have horig : σ'.isOriginalCap = σ.isOriginalCap := (pp_ksm' hm).2.2.1
  have hid : σ'.idleThread = σ.idleThread := congrArg Prod.snd (Vs.gke_preemptionPoint' σ _ hm)
  have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
    ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  have hdead : ∀ p ∈ ZTcb (L := L) Z.th s, DeadP (L := L) H s' p := by
    rintro p ⟨y, hy, zt, n, hz, h65⟩
    rcases J.del.zwf y hy p zt n hz with ⟨-, ht, -⟩ | ⟨h, -, -⟩
    · exact J.deadP_ppw arI hw (J.zH.1 p (J.thT p ht)) (hL.zdead y hy p zt n hz h65)
    · exact absurd h65 h
  refine ⟨hL.of_sameZ hSS hmem horig hid hK J.kern.cs0 hTz hdead, ⟨lst, hDW.of_keep hK fun y hy => ?_⟩,
    hN.of_same (fun y hy => hSS.capV hy) horig⟩
  exact J.ppw_tcbWord arI hw hy (K := 3520#u64) (by simp) (by simp)

/-- **`JAtPreMV` with `LiveDN` at the preempted state** (module docstring):
the ghosts are those of the `JAtZ` before the preemption point. -/
def JAtPreMVL (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64),
    (JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 ∧ Vs.NoSwitch σ0 ∧ PPR0 σ0 ∧ MR a0 σ0.machineState ∧
      ValidMachineTime σ0 ∧ ValidIrqMasks σ0) ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1 ∧
    LiveDN (L := L) Z.th H Cs Z.G s σ

theorem JAtPreMVL.toMV {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPreMVL (L := L) arI AR MR s a σ) :
    JAtPreMV (L := L) arI AR MR s a σ :=
  let ⟨s0, a0, σ0, Z, H, Cs, Ac, Lst, D, ⟨J, h1, h2, h3, h4, h5⟩, hp, hm, _⟩ := h
  ⟨s0, a0, σ0, ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, h1, h2, h3, h4, h5⟩, hp, hm⟩

/-- **The deletion's state after a preemption with liveness** (module
docstring). -/
def WJPML (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  WJP (L := L) arI AR Z H Cs kb s a σ G ∧ JAtPreMVL (L := L) arI AR MR s a σ ∧
    LiveDN (L := L) Z.th H Cs G s σ

theorem WJPML.toM {kb : U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (h : WJPML (L := L) arI AR MR Z H Cs kb s a σ G) : WJPM (L := L) arI AR MR Z H Cs kb s a σ G :=
  ⟨h.1, h.2.1.toMV arI⟩

set_option maxHeartbeats 4000000 in
/-- **The preemption point keeps `WMR MR WJL`, `WJPML` after a preemption**
(module docstring). -/
theorem jPreemptHypLML (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hPA : PPPlatA arI AR) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (hth : Z.th = th) :
    PPHypDW (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPML (L := L) arI AR MR Z H Cs kb) th := by
  intro s a σ G hDS hW
  obtain ⟨⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩, hR, hV, hVI⟩ := hW
  subst hth
  obtain ⟨⟨r1, s', a'⟩, hr, ⟨⟨hSS, σ', hcase, hCR, hWP⟩, -, hw⟩, hK⟩ :=
    spec_exists (WP.spec_and (WP.spec_and (jPreemptHypLM arI hAK hA hnd hM hPA Z H Cs kb rfl s a σ G hDS
      ⟨⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩, hR, hV, hVI⟩)
      (P1.sched.preemption_point.pp hA s a J.blk)) (J.ppDbg hA))
  rw [hr, WP.spec_ok]
  simp only at hSS hcase hCR hWP hw hK ⊢
  refine ⟨hSS, σ', hcase, hCR, ?_⟩
  rcases hcase with ⟨rfl, -⟩ | ⟨rfl, hm⟩
  · exact hWP
  · have hWP' : WJPM (L := L) arI AR MR Z H Cs kb s' a' σ' G := hWP
    have hLv' := J.liveDN_ppw arI hDS ⟨hL, ⟨lst, hDW⟩, hN⟩ hw hK hSS hm
    exact ⟨hWP'.1, ⟨s, a, σ, Z.mv G V, H, Cs, Ac, Lst, D, ⟨J, hns, hp0, hR, hV, hVI⟩, hr, hm, hLv'⟩, hLv'⟩

/-- **The deletion loop's named steps at `MachPlat` with `WJPML`** (module
docstring). -/
theorem delHypsJLML [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hAR : ArchRefines arI AR)
    (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) (hF : JThreadFinHypsU (L := L) arI AR th)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    DelHypsWRZ (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPML (L := L) arI AR MR Z H Cs kb)
      (RdLO (L := L) (A := A) th H) (RzJ (L := L) (A := A) H) th :=
  let h := delHypsJLM arI hT hAR hK hV hF hnd hM hKD hPA hAM Z H Cs kb hth
  ⟨h.fin, h.triv, jPreemptHypLML arI hK hT hnd hM hPA Z H Cs kb hth, h.post, h.zomb, h.swap, h.empty⟩

/-- **The deletion at `MachPlat`, `WJPML` after a preemption** (XTopJointMRDel's
`JDelHypLM` with the liveness at the preempted state). -/
def JDelHypLML (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat), Z.th = th →
    (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) → 6 ≤ K →
    DelHypW (L := L) arI psiD th
      (fun s a σ G => DelE (L := L) Z.th K s σ ∧ WMR MR (WJL (L := L) arI AR Z H Cs kb) s a σ G)
      (fun s a σ G => DelE (L := L) Z.th K s σ ∧ WJPML (L := L) arI AR MR Z H Cs kb s a σ G)

/-- **`JDelHypLML` from `JDelParts`' platform and scope facts and `MachPlat`.** -/
theorem JDelParts.jDelHypLML [Fl4Proofs.P1.PlainStore st] (h : JDelParts (L := L) arI AR th)
    (hT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hAM : ARMask arI AR) :
    JDelHypLML (L := L) arI AR MR th := by
  intro Z H Cs kb K hth hK hK6 s a σ G c hCR hE hA hxm
  obtain ⟨⟨⟨V, Ac, Lst, D, J, -⟩, -⟩, -⟩ := hE.2
  have hP : Placed th := hth ▸ J.xtop.rel.1
  have hH := delHypsJLML arI hT h.archRef h.arKeep h.vt h.thr hnd hM hKD hPA hAM Z H Cs kb hth
  subst hth
  exact delHyp_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 s a σ G c hCR hE hA hxm

/-- **`JAt` with `LiveDN` at its own ghosts** (module docstring). -/
def JAtL (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ LiveDN (L := L) Z.th H Cs Z.G s σ

theorem JAtL.toJAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtL (L := L) arI AR s a σ) :
    JAt (L := L) arI AR s a σ :=
  let ⟨Z, H, Cs, Ac, Lst, D, J, _⟩ := h; ⟨Z, H, Cs, Ac, Lst, D, J⟩

/-- **`DelE` and `WJPML`** (after a preemption). -/
abbrev EJPML (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (K : Nat) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJPML (L := L) arI AR MR Z H Cs kb s a σ G

