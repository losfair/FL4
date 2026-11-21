/-
P3 (DESIGN.md §9), IPC: **what a notification's finalisation keeps of
`JAtZ`'s FL4 words** (toward `JStepHyps.del`), from its footprint `FinW`
(IpcCancelSignals: the scheduler's words `KFoot` and the TCBs' words off the
`MCP`, `YIELD_TO` and IPC-buffer offsets, against the start's SC sizes).

* `finW_cases`: a `FinW` word is in a TCB of `T`, core `c`'s node, a
  notification of `N` or an SC of `C` (`tfoot_tcb`'s cases).
* `JAtZ.finW_keeps`: the TCBs' `MCP`, `YIELD_TO` and IPC-buffer words (`TSW`),
  the SCs' `REPLY` words and the replies' links.
* `JAtZ.finW_scOut`: the header words of `H`'s SCs outside `Z.C` (for the
  dead set; `sc_out_keep`'s argument).
* `JAtZ.finW_irq`: the IRQ node's caps.
* `JAtZ.finW_utc`: the untyped caps' facts, the CDT and original bits kept
  (`sc_utc`'s argument, a TCB word a typed TCB's).
-/
import Fl4Proofs.P3.XTopJointRest
import Fl4Proofs.P3.IpcFinNtfn
import Fl4Proofs.P3.ScSchTailP1
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem finW_cases {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {b : U64} (h : Ipc.FinW (st := st) T N C c s σ b) :
    (∃ y ∈ T, y.val + 256 ≤ b.val ∧ b.val < y.val + 4096) ∨
    (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288) ∨
    (∃ n ∈ N, n.val ≤ b.val ∧ b.val < n.val + 40) ∨ ScObjW C σ b := by
  rcases h with hk | ⟨y, hy, K, h1, h2, -, -, -, e⟩
  · exact tfoot_tcb hS (Or.inl hk)
  · exact Or.inl ⟨y, hy, by omega, by omega⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The frame words a finalisation keeps**: the TCBs' `MCP`, `YIELD_TO` and
IPC-buffer words, the SCs' `REPLY` words, the replies' links. -/
theorem JAtZ.finW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have tsw : ∀ b, Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ b → TSW Z.T Z.C b := fun b hb => Ipc.FinW.tsw hS hb
  refine ⟨fun t ht => hw.mem_eq (mcpA_aligned hT ht) fun hb => ((tsw _ hb).1 t ht).1 (mcpA_val hT ht),
    fun t ht => hw.mem_eq (yieldA_aligned hT ht) fun hb => ((tsw _ hb).1 t ht).2.1 (yieldA_val hT ht),
    fun t ht => hw.mem_eq (tIpcBufA_aligned (hT t ht)) fun hb => ((tsw _ hb).1 t ht).2.2 (tIpcBufA_val (hT t ht)),
    fun q hq => hw.mem_eq (sc_reply_word hS hq).1 fun hb => (tsw _ hb).2 q hq rfl, fun r hr => ?_⟩
  have hal := J.rp.align r hr
  have h8 := rPrevA_val hal
  have h16 := rNextA_val hal
  have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
    hw.mem_eq (J.rp.aligned hr ha) fun hb => by
      rcases hb with hb | ⟨y, hy, K, -, hK, -, -, -, e⟩
      · exact hb.ne_rword hS J.rp hr ha rfl
      · have := J.rp.tcb r hr y hy; omega
  exact ⟨k _ (Or.inl h8), k _ (Or.inr h16)⟩

/-- **The header words of `H`'s SCs outside `Z.C` are kept** by a
finalisation (`sc_out_keep`'s argument). -/
theorem JAtZ.finW_scOut {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) {q : U64} {z : Nat}
    (hq : H q = some (.sc z)) (hqC : q ∉ Z.C) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hfit := hH.fits q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal hfit
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
  rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
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

/-- **The IRQ node's caps are kept** by a finalisation (its words lie in the
kernel-state block; the TCBs, notifications and SCs outside it, the node
after it). -/
theorem JAtZ.finW_irq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) (i : U64) (hi : i.val < 128) :
    capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  refine irqNode_keep hw hkf J.kern.ksbAl (fun b hb => ?_) i hi
  rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
  · simp only [P1.LawfulStore.nodeBase] at g1; omega
  · have := J.nk n hn; omega
  · have := (hS.scOut sc hsc x n hk b ⟨g1, g2⟩).2.2.2; omega

set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after a finalisation**: the caps kept (the slots
same), the free parts zero (no `FinW` word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state, CDT,
original bits and the node-0 `DEBUG_TCBS` word (`hDbg`). -/
theorem JAtZ.finW_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
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
    rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
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
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩

/-- **Core 0's `DEBUG_TCBS` word is kept by P1's footprint** (`KW` leaves it
out; core 0 among the cores, `JKern.cs0`). -/
theorem JAtZ.kw_dbg {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s)) :
    L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
  hw.mem_eq J.kern.dwAl fun hk => P1.dbg0_not_schedW J.blk J.kern.cs0 (Or.inl hk)

/-- **P1's footprint keeps every debug word** (`P1.Foot.dbgKeep`; KENTRY-PLAN
g2i, the `DbgKeep` of the construction sites' `LiveDN` frame). -/
theorem JAtZ.kw_dbgKeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s)) : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
  P1.Foot.dbgKeep J.blk (fun _ h => h) hw

end

end

end Fl4Proofs.P3
