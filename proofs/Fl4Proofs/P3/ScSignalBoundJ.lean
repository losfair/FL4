/-
P3 (DESIGN.md §9), IPC: **`JAtZ` across `send_signal`'s wake-up of the idle
notification's bound thread blocked receiving** (toward `SignalRestJHyp`,
ScSignalJ): the FL4 footprint `CnW` (IpcSignalBound: `FinW`, the endpoints'
two words, the replies' `TCB` words) and the spec frame `CFr`
(IpcSignalBoundFr).

* `JAtZ.cnX_not`: a `CnW` word outside `FinW` lies in an endpoint or a reply
  of `H` (at the reply's `TCB` word), so in no other object of `H`.
* `JAtZ.cnW_keeps`, `cnW_scOut`, `cnW_irq`, `cnW_utc`: XTopJointFinW's
  `finW_*` for `CnW` (the reply links at offsets 8 and 16, not the `TCB`
  word).
* `JAtZ.deadP_cfr`: the dead stay dead (`deadP_nfr` for `CFr`: the changed
  TCB is `t`, not dead (it was blocked receiving); an endpoint holding `t` is
  not idle; a reply naming `t` names a thread).
* `RecvReplyHyp`: a reply naming a thread blocked receiving is on no call
  stack and has null links (`RFree` after the unlink frees it); proved from
  `JAtZ.rrecv` (`recvReplyHyp_holds`).
* `JAtZ.wake_postB`: `JAtZ.wake_post` (ScSignalJ) for `CnW` and `CFr`:
  `CallRel` carried by the call stacks, `reply_sc` and the reply links
  (`CFr.callKeep`), `RFree` by `RecvReplyHyp` for the freed reply.
-/
import Fl4Proofs.P3.ScFireJ
import Fl4Proofs.P3.IpcSignalBound
import Fl4Proofs.P3.IpcSignalBoundSpec
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The threads all sit on the notification's SC's core** (P1's
`DonCore`): the TCBs on core `Z.c` (`SchedCore.aff`), the notification's SC,
when it has one, in `Z.C` (`NSC`) and so on core `Z.c` (`SchedRel.core`). A
wake donation then moves no thread across cores. -/
theorem JAtZ.donCore {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) :
    P1.DonCore st (P1.Heap.tcbs H) (P1.Heap.scs H) n s := by
  intro x _ h0 e y hy
  have hSR := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hSR.lists
  have hyT : y ∈ Z.T := by rw [J.tcbs_eq.1]; exact hy
  have hxC : x ∈ Z.C := by
    have h0' : L.mem s (nScA n) ≠ 0#u64 := by rw [show nScA n = P1.ntfnScA n from rfl, e]; exact h0
    have := NSC.mem J.nsc J.xtop.fin.1.1.2.2.1 hn h0'
    rwa [show nScA n = P1.ntfnScA n from rfl, e] at this
  rw [hc.aff y hyT, Fl4Proofs.P3.Sched.scCoreA_eq, hSR.core x hxC]

/-- `CnW`'s words beyond `FinW`. -/
def CnX (E R : Set U64) (b : U64) : Prop := (∃ e ∈ E, EW e b) ∨ (∃ r ∈ R, b.val = r.val)

/-- **A `CnX` word is in no other object of `H`** (module docstring): not in
an object `p` of `H` other than an endpoint or reply, nor in a reply's words
other than its `TCB` word. -/
theorem JAtZ.cnX_not (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : CnX Z.E Z.R b)
    {p : U64} {k : P1.HKind} (hp : H p = some k) (h1 : p.val ≤ b.val) (h2 : b.val < p.val + 2 ^ k.bits)
    (hk : (k ≠ .ep ∧ k ≠ .reply) ∨ (k = .reply ∧ b.val ≠ p.val)) : False := by
  have hH := J.kern.heap
  obtain ⟨q, kq, hq, g1, g2, hkq⟩ : ∃ q kq, H q = some kq ∧ q.val ≤ b.val ∧ b.val < q.val + 2 ^ kq.bits ∧
      (kq = .ep ∨ (kq = .reply ∧ b.val = q.val)) := by
    rcases hb with ⟨e, he, h⟩ | ⟨r, hr, h⟩
    · refine ⟨e, .ep, J.zH.2.1 e he, ?_, ?_, Or.inl rfl⟩ <;> (unfold EW at h; (try simp only [P1.HKind.bits]); omega)
    · exact ⟨r, .reply, J.zH.2.2.1 r hr, by omega, by simp only [P1.HKind.bits]; omega, Or.inr ⟨rfl, h⟩⟩
  by_cases e : p = q
  · subst e
    rw [hp] at hq; cases hq
    rcases hk with ⟨k1, k2⟩ | ⟨k1, k2⟩ <;> rcases hkq with k3 | ⟨k3, k4⟩
    · exact k1 k3
    · exact k2 k3
    · rw [k1] at k3; cases k3
    · exact k2 k4
  · have := hH.disj p k q kq hp hq e
    omega

theorem JAtZ.cnW_cases (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (h : CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b) :
    FinW (st := st) Z.T Z.N Z.C Z.c s σ b ∨ CnX Z.E Z.R b := h.imp_right id

/-- **A `CnW` word is no TCB's VCPU word** (KENTRY-PLAN g2b). -/
theorem JAtZ.cnW_nv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (hb : CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b) : ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  have hS := J.xtop.fin.1.1.1
  intro t ht
  rcases hb with hb | hx
  · exact FinW.nv hS hb t ht
  · rintro rfl
    obtain ⟨Q, R0, hc, -⟩ := hS.lists
    have hv : (tVcpuA t).val = t.val + 3664 := tfield_val (hc.tcbs t ht) (K := 3664#u64) (by simp)
    exact J.cnX_not hx (J.zH.1 t ht) (by omega) (by simp only [P1.HKind.bits]; omega)
      (Or.inl ⟨fun e => (by cases e), fun e => (by cases e)⟩)

/-- **The frame words a `CnW` step keeps** (`finW_keeps`). -/
theorem JAtZ.cnW_keeps (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have tsw : ∀ b, FinW (st := st) Z.T Z.N Z.C Z.c s σ b → TSW Z.T Z.C b := fun b hb => FinW.tsw hS hb
  have tcbX : ∀ t ∈ Z.T, ∀ b : U64, b.val = t.val + 3440 ∨ b.val = t.val + 3472 ∨ b.val = t.val + 3512 →
      ¬ CnX Z.E Z.R b := fun t ht b hv hx =>
    J.cnX_not hx (J.zH.1 t ht) (by omega) (by simp only [P1.HKind.bits]; omega)
      (Or.inl ⟨fun e => (by cases e), fun e => (by cases e)⟩)
  refine ⟨fun t ht => hw.mem_eq (mcpA_aligned hT ht) fun hb => ?_,
    fun t ht => hw.mem_eq (yieldA_aligned hT ht) fun hb => ?_,
    fun t ht => hw.mem_eq (tIpcBufA_aligned (hT t ht)) fun hb => ?_,
    fun q hq => hw.mem_eq (sc_reply_word hS hq).1 fun hb => ?_, fun r hr => ?_⟩
  · rcases hb with hb | hb
    · exact ((tsw _ hb).1 t ht).1 (mcpA_val hT ht)
    · exact tcbX t ht _ (Or.inl (mcpA_val hT ht)) hb
  · rcases hb with hb | hb
    · exact ((tsw _ hb).1 t ht).2.1 (yieldA_val hT ht)
    · exact tcbX t ht _ (Or.inr (Or.inl (yieldA_val hT ht))) hb
  · rcases hb with hb | hb
    · exact ((tsw _ hb).1 t ht).2.2 (tIpcBufA_val (hT t ht))
    · exact tcbX t ht _ (Or.inr (Or.inr (tIpcBufA_val (hT t ht)))) hb
  · rcases hb with hb | hb
    · exact (tsw _ hb).2 q hq rfl
    · obtain ⟨Q', R', -, hs⟩ := hS.lists
      obtain ⟨y, n, hky, -⟩ := hs.scs q hq
      have hHq := (hJ.sc q y n (J.c0 q hq) hky).2
      have hz := J.kern.heap.scmin q _ hHq
      have h128 : 2 ^ 7 ≤ 2 ^ (n + Fl4Spec.minSchedContextBits) := Nat.pow_le_pow_right (by norm_num) hz
      have hv := (sc_reply_word hS hq).2.1
      exact J.cnX_not hb hHq (by omega) (by simp only [P1.HKind.bits]; omega)
        (Or.inl ⟨fun e => (by cases e), fun e => (by cases e)⟩)
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      hw.mem_eq (J.rp.aligned hr ha) fun hb => by
        rcases hb with (hb | ⟨y, hy, K, -, hK, -, -, -, e⟩) | hb
        · exact hb.ne_rword hS J.rp hr ha rfl
        · have := J.rp.tcb r hr y hy; omega
        · exact J.cnX_not hb (J.zH.2.2.1 r hr) (by omega) (by simp only [P1.HKind.bits]; omega)
            (Or.inr ⟨rfl, by omega⟩)
    exact ⟨k _ (Or.inl h8), k _ (Or.inr h16)⟩

/-- **The header words of `H`'s SCs outside `Z.C` are kept** by a `CnW` step. -/
theorem JAtZ.cnW_scOut (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ)) {q : U64} {z : Nat}
    (hq : H q = some (.sc z)) (hqC : q ∉ Z.C) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hfit := hH.fits q _ hq
  simp only [P1.HKind.bits] at hfit
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
  rcases hb with hb | hb
  · rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hHy : H y = some .tcb := J.zH.1 y hy
      have hne : q ≠ y := fun e => by rw [e, hHy] at hq; cases hq
      have := hH.disj q _ y _ hq hHy hne
      simp only [P1.HKind.bits] at this
      omega
    · have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
      have := J.kern.hnd q _ hq Z.c hcC
      simp only [P1.HKind.bits] at this
      omega
    · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
      have hne : q ≠ n := fun e => by rw [e, hHn] at hq; cases hq
      have := hH.disj q _ n _ hq hHn hne
      simp only [P1.HKind.bits] at this
      omega
    · have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
      have hne : q ≠ sc := fun e => hqC (e ▸ hsc)
      have := hH.disj q _ sc _ hq hHs hne
      simp only [P1.HKind.bits] at this
      omega
  · exact J.cnX_not hb hq (by omega) (by simp only [P1.HKind.bits]; omega)
      (Or.inl ⟨fun e => (by cases e), fun e => (by cases e)⟩)

/-- **The IRQ node's caps are kept** by a `CnW` step. -/
theorem JAtZ.cnW_irq (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ)) (i : U64) (hi : i.val < 128) :
    capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  refine irqNode_keep hw hkf J.kern.ksbAl (fun b hb => ?_) i hi
  rcases hb with hb | hb
  · rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
    · simp only [P1.LawfulStore.nodeBase] at g1; omega
    · have := J.nk n hn; omega
    · have := (hS.scOut sc hsc x n hk b ⟨g1, g2⟩).2.2.2; omega
  · rcases hb with ⟨e, he, h⟩ | ⟨r, hr, h⟩
    · have := hJ.ks e _ (J.zH.2.1 e he) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; unfold EW at h; omega
    · have := hJ.ks r _ (J.zH.2.2.1 r hr) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega

set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after a `CnW` step** (`finW_utc`; the endpoints
and replies are spec objects, outside the free parts, `SpecFree`). -/
theorem JAtZ.cnW_utc (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (harch : σ'.archState = σ.archState)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [harch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases hb with hb | hb
    · rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
      · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
        have := U.free y .tcb hth
        simp only [objSize] at this; omega
      · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
        omega
      · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
        have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) n.bv _ hx
        simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
        omega
      · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
        simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
        rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
        omega
    · rcases hb with ⟨e, he, h⟩ | ⟨r, hr, h⟩
      · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.ep e he
        have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) e.bv _ hx
        simp only [Fl4Spec.objBits, Fl4Spec.endpointBits, UScalar.bv_toNat] at this
        unfold EW at h
        omega
      · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hr
        have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) r.bv _ hx
        simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this
        omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a `CFr` step** with the footprint `CnW`
(`deadP_nfr`; `t` was blocked receiving, so not dead). -/
theorem JAtZ.deadP_cfr (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {r t : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : CFr r t σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x n hx => ?_) (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hw hz hqC hK8 hK)
    F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: its state and (null) bound notification kept
    obtain ⟨t', ht', e⟩ := J.obj.tcb q.bv x hx
    have htq : t' = q := P1.eq_of_bv e
    subst htq
    obtain ⟨-, -, d3, -, -⟩ := hd.1 (J.zH.1 t' ht')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t' ht'
    rw [hx] at hk'; cases hk'
    have hbn : x.tcbBoundNotification = none := by
      rw [hR.bound, show tBoundA t' = P1.boundA t' from rfl, d3, optRef_zero]
    obtain ⟨st', bn, fl, ar, hk3, hs⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, ?_, Or.inl rfl⟩
    · show st' = x.tcbState
      rcases hs with ⟨⟨e, -⟩ | ⟨-, e, -⟩, -, -⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e] at h0; simp [tsCode] at h0
      · exact absurd e (ht t' hq)
    · show bn = x.tcbBoundNotification
      rcases hs with ⟨-, -, e | e⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e, hbn]
      · exact absurd e (ht t' hq)
  · -- a dead endpoint: idle, so holding nobody
    obtain ⟨y, hy, hc⟩ := F.epF hx
    rcases hc with rfl | ⟨-, hm⟩
    · exact hy
    · exfalso
      obtain ⟨e', he', e⟩ := J.obj.ep q.bv x hx
      have heq : e' = q := P1.eq_of_bv e
      subst heq
      have d2 := hd.2.1 (J.zH.2.1 e' he')
      obtain ⟨x', hk', hO⟩ := J.xtop.ipc.toE.ep e' he'
      rw [hx] at hk'; cases hk'
      rw [epState_eq] at d2
      cases x with
      | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hm
      | sendEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
      | recvEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
  · -- a dead notification: not waiting, unbound
    obtain ⟨n', hn', e⟩ := J.obj.ntfn q.bv x hx
    have hnq : n' = q := P1.eq_of_bv e
    subst hnq
    obtain ⟨d1, d2, -⟩ := hd.2.2.1 (J.zH.2.2.2 n' hn')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.toN.ntfn n' hn'
    rw [hx] at hk'; cases hk'
    obtain ⟨y, hy, -, hobj, hbd, hsc'⟩ := F.ntfnF hx
    have hbn : x.ntfnBoundTcb = none := by
      rw [hR.bound, show nBoundA n' = P1.ntfnBtA n' from rfl, d2, optRef_zero]
    have hnw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := by
      intro l e
      have hO := hR.obj
      rw [e] at hO
      exact d1 (by rw [epState_eq]; exact hO.1)
    refine ⟨y, hy, (hobj hnw).imp id And.right, ?_, hsc'⟩
    rcases hbd with e | e
    · exact e
    · rw [e, hbn]
  · -- a dead reply: naming nobody
    obtain ⟨y, hy, -, hc⟩ := F.replyF hx
    refine ⟨y, hy, ?_⟩
    rcases hc with e | ⟨hxt, -⟩
    · exact e
    · exfalso
      obtain ⟨r', hr', e⟩ := J.obj.reply q.bv x hx
      have heq : r' = q := P1.eq_of_bv e
      subst heq
      have d4 := hd.2.2.2.1 (J.zH.2.2.1 r' hr')
      obtain ⟨x', hk', hx'⟩ := J.xtop.ipc.toE.reply r' hr'
      rw [hx] at hk'; cases hk'
      have d4' : L.mem s (Endp.rTcbA r') = 0#u64 := d4
      rw [hx', d4', optRef_zero] at hxt
      cases hxt
  · -- an SC: its thread kept, its notification kept or cut
    obtain ⟨rf, nt, hk3, -, hn⟩ := F.scF hx
    exact ⟨_, hk3, Or.inl rfl, hn⟩

/-- `NoDon` across a `CFr` step (the TCBs' SCs, the notifications' SCs kept or
cut, the SCs' threads kept). -/
theorem NoDon.cfr {C : Set U64} {r t u m : Fl4Spec.ObjRef} {σ1 σ2 : Fl4Spec.State Unit} (F : CFr r t σ1 σ2)
    (h : NoDon C σ1 u m) : NoDon C σ2 u m := by
  intro xt xn h1 h2
  obtain ⟨x0, st', bn, fl, ar, hx0, rfl, -⟩ := F.tcbB h1
  obtain ⟨xn0, hxn0, -, -, hsc, -, -⟩ := F.ntfnB h2
  rcases hsc with e | e
  · rcases h x0 xn0 hx0 hxn0 with h' | h' | ⟨cq, hcq, h3, y, k, hky, hyt⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl (e.trans h'))
    · obtain ⟨rf, nt, hky', -⟩ := F.scF hky
      exact Or.inr (Or.inr ⟨cq, hcq, e.trans h3, _, k, hky', hyt⟩)
  · exact Or.inr (Or.inl e)

variable (arI) in
/-- **A reply naming a thread blocked receiving is detached and unlinked**
(module docstring): on no call stack and with null `prev`/`next` words, at
every `JAtZ` (`recvReplyHyp_holds`, from `JAtZ.rrecv`). -/
def RecvReplyHyp (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → ∀ d ∈ Z.R, ∀ xr t xt, σ.kheap d.bv = some (.reply xr) →
      xr.replyTcb = some t → σ.kheap t = some (.tcb xt) → Fl4Spec.receiveBlocked xt.tcbState = true →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64

/-- **`RecvReplyHyp` holds** (formerly the [J] premise `RecvReplyLinksHyp`):
`JAtZ.rrecv` (ScRecvLinks) gives the null links, `detached_of_next0` the
rest. -/
theorem recvReplyHyp_holds : RecvReplyHyp (L := L) arI AR H Cs := by
  intro Z Ac Lst D s a σ J d hd xr t xt hx ht hxt hrb
  obtain ⟨hn, hp⟩ := J.rrecv d hd ⟨xr, t, xt, hx, ht, hxt, hrb⟩
  exact ⟨detached_of_next0 J.call (fun r hr => (J.rp.align r hr).2.1) hn, hn, hp⟩

set_option maxHeartbeats 8000000 in
/-- **The bound-receiver wake keeps `JAtZ`** (module docstring). -/
theorem JAtZ.wake_postB (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n t : Fl4Spec.ObjRef}
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : CFr n t σ σ') (I3 : Inv σ') (B3 : BlockedScActive σ') (hAI3 : ActIdle σ')
    (hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') (hrun3 : CurRunM σ')
    (hRR : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb = some t →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hw
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨x, hx, -, hc⟩ := F.replyB hy
    obtain ⟨e1, e2⟩ := k4 d hd
    rcases hc with e | ⟨hxt, -⟩
    · obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨x, hx, e ▸ hyt⟩
      exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
    · obtain ⟨h1, h2, h3⟩ := hRR d hd x hx hxt
      exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_cfr F hS3 hIR.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep ht
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have hRR' := J.rrecv.frame k4 F.khrb
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.cnW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, B3, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩

set_option maxHeartbeats 8000000 in
/-- **`send_signal` to an idle notification bound to a thread blocked
receiving, without SC donation, keeps `JAtZ`** (module docstring): FL4's side
`send_signal_bound_irel`, the spec's `cancelIpc_recv_cfr`, `cancel_recv_inv`,
`wake_specB`, then `wake_postB`. -/
theorem JAtZ.signal_boundJ (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn) {t : U64} {tcb : Fl4Spec.Tcb}
    (hb : x.ntfnBoundTcb = some t.bv) (hkt : σ.kheap t.bv = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) (hND : NoDon Z.C σ t.bv n.bv) (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hNt : ∀ m ∈ P1.Heap.ntfns H, H m = some .ntfn := fun _ h => h
  have hnH : n ∈ P1.Heap.ntfns H := J.zH.2.2.2 n hn
  have hx := J.xtop.ipc.toN.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := Notif.optRef_some (hx.bound ▸ hb)
  have htU : L.mem s (nBoundA n) = t := P1.eq_of_bv hbt
  have htT : t ∈ Z.T := htU ▸ hx.bound_mem hb0
  obtain ⟨e, ro, d, hst⟩ : ∃ e ro d, tcb.tcbState = .blockedOnReceive e ro d := by
    cases h : tcb.tcbState <;> simp [h, Fl4Spec.receiveBlocked] at hrb
    exact ⟨_, _, _, rfl⟩
  have hCR : ∀ t', t' = t → CancelRecvHyp Z.E (L.mem s) σ t' tcb := fun t' et => et ▸
    cancelRecvHyp_of hI.1.toE J.sv J.obj J.inv htT hkt hrb
  have hCR0 := hCR t rfl
  obtain ⟨xe, hke, hqe⟩ := hCR0.ok.2.1 _ ro d hst
  have hro : ∀ rp, ro = some rp → ∃ xr, σ.kheap rp = some (.reply xr) ∧ xr.replyTcb = some t.bv := fun rp er => by
    subst er; exact hCR0.ok.2.2.1 _ rp d hst
  have hrbI : RbIn tcb.tcbState := Or.inl ⟨_, _, _, hst⟩
  have post1 : ∀ σ1 x1, Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) →
      σ1.kheap t.bv = some (.tcb x1) → x1.tcbState = .inactive → RelIfBound σ1 t.bv →
      CFr n.bv t.bv σ σ1 ∧ Inv σ1 ∧ ((), σ1) ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by
    intro σ1 x1 hc hk1 hin hrib
    have hm : ((), σ1) ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by rw [hc]; exact Set.mem_singleton _
    obtain ⟨F1, -, -⟩ := cancelIpc_recv_cfr (r := n.bv) hkt hst hke hqe hro hm
    exact ⟨F1, cancel_recv_inv J.inv hkt hrbI hm hrib, hm⟩
  have hA3 : ∀ σ1 x1, Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) →
      σ1.kheap t.bv = some (.tcb x1) → x1.tcbState = .inactive → RelIfBound σ1 t.bv →
      ActReady (wakeSt3 σ1 t.bv x1 badge.bv) ∧ NoDon Z.C σ1 t.bv n.bv := by
    intro σ1 x1 hc hk1 hin hrib
    obtain ⟨F1, hI1, -⟩ := post1 σ1 x1 hc hk1 hin hrib
    exact ⟨(wake_inv3B hI1 hk1 hin hrib badge.bv).actReady, NoDon.cfr F1 hND⟩
  refine WP.spec_mono (WP.spec_and (send_signal_bound_irel J.ip s a σ hI hn hk hidle hb hkt hrb badge hCR hA3)
    (P1.notification.send_signal.tinvF hAT s a n badge J.blk hnH (hNt n hnH))) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, s1, σ1, σ', x1, hc, hk1, hin, hrib, hX1, hF1, hW1, hdon, hsend, hmw, hIR, hF2, hFS⟩, hbk⟩
  try simp only [WP.uncurry'_pair] at hbk
  obtain ⟨hbk, -, hfoot⟩ := hbk
  have hfoot := hfoot (J.donCore hn)
  subst ea
  obtain ⟨F1, hI1, hm1⟩ := post1 σ1 x1 hc hk1 hin hrib
  obtain ⟨-, hk1', hact1⟩ := cancelIpc_recv_cfr (r := n.bv) hkt hst hke hqe hro hm1
  have hB1 := F1.bsa J.bsa
  have hAI1 : ActIdle σ1 := by
    refine ⟨fun u hu => ?_, F1.idleOK J.act.2⟩
    rcases hact1 with e1 | e1
    · exact F1.sched (J.act.1 u (by rw [← e1]; exact hu))
    · rw [e1] at hu; cases hu
  have hcn : σ.schedulerAction = .chooseNewThread → σ1.schedulerAction = .chooseNewThread := fun e0 => by
    rcases hact1 with e1 | e1
    · rw [e1, e0]
    · exact e1
  have hcur1 : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1 := J.cur.imp hcn F1.curInv
  have hrun1 : CurRunM σ1 := J.curRun.of_cn F1.curRunW hact1.symm
  have hx1 : x1 = { tcb with tcbFault := none, tcbState := .inactive } := by
    rw [hk1] at hk1'; cases hk1'; rfl
  have hsa : ∀ p y k, x1.tcbSchedContext = some p → σ1.kheap p = some (.schedContext y k) →
      Fl4Spec.scActive y = true := by
    intro p y k hp hky
    rw [hx1] at hp
    obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := F1.scB hky
    obtain ⟨y', k', hky', hyt⟩ := J.inv.back t.bv tcb p hkt hp
    rw [hy0] at hky'; cases hky'
    exact J.bsa.tcb p y0 k t.bv tcb hy0 hyt hkt (by rw [hst]; rfl)
  obtain ⟨I', B', F2, AI', cur', run'⟩ := wake_specB hI1 hB1 hAI1 hcur1 hrun1 hk1 hin hrib hsa hdon hmw
  have hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    (hW1.trans (hFS.1.mono fun b hb => FinW.back hW1.1 (SzKeepC.of F1.szKeep) hb)).mono
      fun b h => h.elim id Or.inl
  have hRR : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb = some t.bv →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64 :=
    fun d hd xr hx' hxt => recvReplyHyp_holds Z Ac Lst D s _ σ J d hd xr t.bv tcb hx' hxt hkt hrb
  have htD : ∀ q ∈ D, q.bv ≠ t.bv := by
    intro q hq eq
    have hqt : q = t := P1.eq_of_bv eq
    subst hqt
    have d1 := ((J.jcov.dead q hq).1 (J.zH.1 q htT)).1
    have h3 := (hI.1.toN.at_tcb htT hkt).st
    rw [P1.stA_eq, ← tStA_eq] at d1
    rw [d1, hst] at h3
    unfold sched.TS_INACTIVE at h3
    simp [tsCode] at h3
  obtain ⟨V', J'⟩ := J.wake_postB hIR (hF1.trans hF2) hw hbk hfoot (F1.trans F2) I' B' AI' cur' run' hRR htD
  exact ⟨σ', V', Ac, Lst, D, hsend, (F1.trans F2).sk.dt, J'⟩

end

end

end Fl4Proofs.P3
