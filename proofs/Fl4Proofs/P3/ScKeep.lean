/-
P3 (DESIGN.md §9), scheduling contexts: **what the SchedContext paths keep**.

Spec side, from `SOK` (ScPres.lean): the yield-to fields (`YKeep`), the
MCPs (`McpKeep`), the call stacks (`CKeep`), the CNodes and TCB caps
(`StateRel`), `KSub`.

FL4 side, from the footprints (`KFoot`, `TFoot`, `RFoot`) and the
placement in `SchedRel`/`RPlaced`: the `MCP`, `YIELD_TO`, SC `REPLY` and
reply link words are kept (`KFoot.keep` and friends), and so are the cap
slots of a typed heap whose slots lie apart from the scheduler's objects
(`SlotsApart`, `slotsSame_of_ufoot`).
-/
import Fl4Proofs.P3.ScMcp
import Fl4Proofs.P3.ScPresOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-! ## The spec side -/

section Spec
open Fl4Spec

theorem SOK.fwd {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') {p : ObjRef} {o : KernelObject}
    (hp : σ.kheap p = some o) : ∃ o', σ'.kheap p = some o' ∧ PK f o o' := by
  have := h.kh p
  rw [hp] at this
  cases h' : σ'.kheap p with
  | none => rw [h'] at this; exact this.elim
  | some o' => rw [h'] at this; exact ⟨o', rfl, this⟩

theorem SOK.bwd {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') {p : ObjRef} {o' : KernelObject}
    (hp : σ'.kheap p = some o') : ∃ o, σ.kheap p = some o ∧ PK f o o' := by
  have := h.kh p
  rw [hp] at this
  cases h' : σ.kheap p with
  | none => rw [h'] at this; exact this.elim
  | some o => rw [h'] at this; exact ⟨o, rfl, this⟩

theorem SOK.none {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') {p : ObjRef} (hp : σ.kheap p = none) :
    σ'.kheap p = none := by
  have := h.kh p
  rw [hp] at this
  cases h' : σ'.kheap p with
  | none => rfl
  | some o' => rw [h'] at this; exact this.elim

theorem PK.tcb_inv {f : Bool × Bool} {x : Tcb} {o : KernelObject} (h : PK f (.tcb x) o) :
    ∃ y, o = .tcb y ∧ y.tcbCtable = x.tcbCtable ∧ y.tcbVtable = x.tcbVtable ∧ y.tcbIpcframe = x.tcbIpcframe ∧
      y.tcbFaultHandler = x.tcbFaultHandler ∧ y.tcbTimeoutHandler = x.tcbTimeoutHandler ∧ y.tcbEpt = x.tcbEpt ∧
      y.tcbMcpriority = x.tcbMcpriority ∧ (f.1 = true → y.tcbYieldTo = x.tcbYieldTo) := by
  cases o <;> simp only [PK] at h
  exact ⟨_, rfl, h⟩

theorem PK.sc_inv {f : Bool × Bool} {x : SchedContext} {n : Nat} {o : KernelObject}
    (h : PK f (.schedContext x n) o) :
    ∃ y, o = .schedContext y n ∧ (f.1 = true → y.scYieldFrom = x.scYieldFrom) ∧
      (f.2 = true → y.scReplies = x.scReplies) := by
  cases o <;> simp only [PK] at h
  obtain ⟨rfl, h⟩ := h
  exact ⟨_, rfl, h⟩

theorem PK.reply_inv {f : Bool × Bool} {x : Reply} {o : KernelObject} (h : PK f (.reply x) o) :
    ∃ y, o = .reply y ∧ (f.2 = true → y.replySc = x.replySc ∧ y.replyTcb = x.replyTcb) := by
  cases o <;> simp only [PK] at h
  exact ⟨_, rfl, h⟩

theorem PK.cnode_inv {f : Bool × Bool} {r : Nat} {cs : CnodeContents} {o : KernelObject}
    (h : PK f (.cnode r cs) o) : o = .cnode r cs := by
  simp only [PK] at h; exact h

theorem PK.sc_back {f : Bool × Bool} {y : SchedContext} {n : Nat} {o : KernelObject}
    (h : PK f o (.schedContext y n)) :
    ∃ x, o = .schedContext x n ∧ (f.1 = true → y.scYieldFrom = x.scYieldFrom) := by
  cases o <;> simp only [PK, reduceCtorEq] at h
  obtain ⟨rfl, h, -⟩ := h
  exact ⟨_, rfl, h⟩

theorem PK.cnode_back {f : Bool × Bool} {r : Nat} {cs : CnodeContents} {o : KernelObject}
    (h : PK f o (.cnode r cs)) : o = .cnode r cs := by
  cases o <;> simp only [PK, reduceCtorEq] at h
  exact h.symm

theorem PK.tcb_back {f : Bool × Bool} {y : Tcb} {o : KernelObject} (h : PK f o (.tcb y)) : ∃ x, o = .tcb x := by
  cases o <;> simp only [PK, reduceCtorEq] at h
  exact ⟨_, rfl⟩

theorem SOK.ykeep {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') (hf : f.1 = true) : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p x n hp => ?_, fun p y n hp => ?_⟩
  · obtain ⟨o', h1, h2⟩ := h.fwd hp
    obtain ⟨y, rfl, -, -, -, -, -, -, -, e⟩ := h2.tcb_inv
    exact ⟨y, h1, e hf⟩
  · obtain ⟨o', h1, h2⟩ := h.fwd hp
    obtain ⟨y, rfl, e, -⟩ := h2.sc_inv
    exact ⟨y, h1, e hf⟩
  · obtain ⟨o, h1, h2⟩ := h.bwd hp
    obtain ⟨x, rfl, e⟩ := h2.sc_back
    exact ⟨x, h1, e hf⟩

theorem SOK.mcpKeep {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') : McpKeep σ σ' := by
  intro p x hp
  obtain ⟨o', h1, h2⟩ := h.fwd hp
  obtain ⟨y, rfl, -, -, -, -, -, -, e, -⟩ := h2.tcb_inv
  exact ⟨y, h1, e⟩

theorem SOK.ckeep {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') (hf : f.2 = true) : CKeep σ σ' := by
  refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun p x n hp => ?_⟩
  · obtain ⟨o', h1, h2⟩ := h.fwd hq
    obtain ⟨y', rfl, -, e⟩ := h2.sc_inv
    exact ⟨y', h1, e hf⟩
  · obtain ⟨o', h1, h2⟩ := h.fwd hq
    obtain ⟨x', rfl, e⟩ := h2.reply_inv
    exact ⟨x', h1, (e hf).1, (e hf).2⟩
  · obtain ⟨o, h1, h2⟩ := h.bwd hp
    obtain ⟨x0, rfl, -⟩ := h2.sc_back
    exact ⟨x0, h1⟩

theorem SOK.szKeep {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') : SzKeep σ σ' := by
  intro p x n hp
  obtain ⟨o, h1, h2⟩ := h.bwd hp
  obtain ⟨x0, rfl, -⟩ := h2.sc_back
  exact ⟨x0, h1⟩

theorem SOK.ksub {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun r cs hc hw => ?_, fun t ht => ?_, fun hn => h.none hn⟩
  · obtain ⟨o0, h1, h2⟩ := h.bwd hc
    rw [h2.cnode_back] at h1
    exact ⟨cs, h1, hw⟩
  · obtain ⟨o0, h1, h2⟩ := h.bwd ht
    obtain ⟨x, rfl⟩ := h2.tcb_back
    exact ⟨x, h1⟩

theorem tcbCnodeMap_congr {x y : Tcb} (h1 : y.tcbCtable = x.tcbCtable) (h2 : y.tcbVtable = x.tcbVtable)
    (h3 : y.tcbIpcframe = x.tcbIpcframe) (h4 : y.tcbFaultHandler = x.tcbFaultHandler)
    (h5 : y.tcbTimeoutHandler = x.tcbTimeoutHandler) (h6 : y.tcbEpt = x.tcbEpt) : tcbCnodeMap y = tcbCnodeMap x := by
  unfold tcbCnodeMap; rw [h1, h2, h3, h4, h5, h6]

end Spec

theorem SOK.stateRel {f : Bool × Bool} {th : TypedHeap} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (h : SOK f σ σ') (hR : StateRel th m σ) : StateRel th m σ' := by
  refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
  · obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode p r hp
    obtain ⟨o', h1, h2⟩ := h.fwd hk
    rw [h2.cnode_inv] at h1
    exact ⟨cs, h1, hwf, hs⟩
  · obtain ⟨x, hk, hs⟩ := hR.tcb t ht
    obtain ⟨o', h1, h2⟩ := h.fwd hk
    obtain ⟨y, rfl, e1, e2, e3, e4, e5, e6, -, -⟩ := h2.tcb_inv
    exact ⟨y, h1, fun i hi => by rw [tcbCnodeMap_congr e1 e2 e3 e4 e5 e6]; exact hs i hi⟩

/-! ## The FL4 side -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem yieldA_val {T : Set U64} (hT : TcbPlaced T) {t : U64} (ht : t ∈ T) : (yieldA t).val = t.val + 3472 :=
  tfield_val (hT t ht) (K := 3472#u64) (by simp)

theorem mcpA_val {T : Set U64} (hT : TcbPlaced T) {t : U64} (ht : t ∈ T) : (mcpA t).val = t.val + 3440 :=
  tfield_val (hT t ht) (K := 3440#u64) (by simp)

/-- A `KFoot` word is no TCB word at an offset outside `SOff`. -/
theorem KFoot.ne_tcbw {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {b : U64} (hb : KFoot st T N C c s σ b) {t : U64} (ht : t ∈ T) {K : U64} (hK : K.val < 4096)
    (hKs : ¬ SOff K) : b ≠ core.num.U64.wrapping_add t K := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hv := tfield_val (hT t ht) hK
  rintro rfl
  rcases hb with (⟨y, hy, K', hK', e⟩ | ⟨g1, g2⟩) | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, ho, -⟩
  · rw [tt_eq_iff (hT t ht) (hT y hy) hK hK'.2.1] at e
    obtain ⟨rfl, rfl⟩ := e
    exact hKs hK'
  · have := hc.node.disj t ht; rw [hv] at g1 g2; omega
  · have := hS.placed.disj n hn t ht; rw [hv] at g1 g2; omega
  · have := (hS.scOut sc hsc x n hk _ ho).2.2.1 t ht; rw [hv] at this; omega

/-- A `KFoot` word is no `MCP` word. -/
theorem KFoot.ne_mcp {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {b : U64} (hb : KFoot st T N C c s σ b) {t : U64} (ht : t ∈ T) : b ≠ mcpA t :=
  hb.ne_tcbw hS ht (K := 3440#u64) (by simp) (fun h => h.2.2.1 rfl)

/-- A `KFoot` word is no `YIELD_TO` word. -/
theorem KFoot.ne_yield {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {b : U64} (hb : KFoot st T N C c s σ b) {t : U64} (ht : t ∈ T) : b ≠ yieldA t :=
  hb.ne_tcbw hS ht (K := 3472#u64) (by simp) (fun h => h.2.2.2 rfl)

/-- A `KFoot` word is no SC `REPLY` word. -/
theorem KFoot.ne_screply {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {b : U64} (hb : KFoot st T N C c s σ b) {q : U64} (hq : q ∈ C) :
    b ≠ scReplyA q := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xq, nq, hkq, hxq⟩ := hs.scs q hq
  obtain ⟨-, hv, hsz⟩ := sc_reply_word hS hq
  have hin : ScObj q nq (scReplyA q) := by have := hsz xq nq hkq; unfold ScObj; rw [hv]; omega
  obtain ⟨hnw, hnd, htc, -⟩ := hS.scOut q hq xq nq hkq _ hin
  rintro rfl
  rcases hb with hb | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, ho, hne⟩
  · rcases hb.range hc.tcbs with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
    · have := htc y hy; omega
    · omega
  · exact hnw (Or.inl ⟨n, hn, g1, g2⟩)
  · by_cases e : sc = q
    · subst e; exact hne rfl
    · exact hS.scDisj sc hsc q hq e x n xq nq hk hkq _ ho hin

/-- A `KFoot` word is no reply link word. -/
theorem KFoot.ne_rword {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) {b : U64} (hb : KFoot st T N C c s σ b)
    {r : U64} (hr : r ∈ R) {a : U64} (ha : a.val = r.val + 8 ∨ a.val = r.val + 16) : b ≠ a := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have k1 := hRP.ksb r hr
  rintro rfl
  rcases hb with hb | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, ⟨g1, g2⟩, -⟩
  · rcases hb.range hc.tcbs with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
    · have := hRP.tcb r hr y hy; omega
    · simp only [LawfulStore.nodeBase] at k1 g1 g2; omega
  · have := hRP.ntfn r hr n hn; omega
  · have := hRP.sc r hr sc hsc x n hk; omega

/-- **What a `KFoot` step keeps**: the `MCP`, `YIELD_TO`, SC `REPLY` and
reply link words. -/
theorem KFoot.keep {N T C R : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ)
    (hw : WritesIn st s s' (KFoot st T N C c s σ)) :
    (∀ t ∈ T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ q ∈ C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  refine ⟨fun t ht => hw.mem_eq (mcpA_aligned hT ht) fun hb => hb.ne_mcp hS ht rfl,
    fun t ht => hw.mem_eq (yieldA_aligned hT ht) fun hb => hb.ne_yield hS ht rfl,
    fun q hq => hw.mem_eq (sc_reply_word hS hq).1 fun hb => hb.ne_screply hS hq rfl, fun r hr => ?_⟩
  have hA := hRP.align r hr
  exact ⟨hw.mem_eq (hRP.aligned hr (Or.inl (rPrevA_val hA))) fun hb => hb.ne_rword hS hRP hr (Or.inl (rPrevA_val hA)) rfl,
    hw.mem_eq (hRP.aligned hr (Or.inr (rNextA_val hA))) fun hb => hb.ne_rword hS hRP hr (Or.inr (rNextA_val hA)) rfl⟩

/-- A `YIELD_TO` word is no `MCP`, SC `REPLY` or reply link word. -/
theorem YW.ne {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    (hRP : RPlaced st N T C R c s σ) {b : U64} (hb : YW T b) :
    (∀ t ∈ T, b ≠ mcpA t) ∧ (∀ q ∈ C, b ≠ scReplyA q) ∧
    (∀ r ∈ R, ∀ a : U64, (a.val = r.val + 8 ∨ a.val = r.val + 16) → b ≠ a) := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  obtain ⟨y, hy, rfl⟩ := hb
  have hv := yieldA_val hT hy
  refine ⟨fun t ht e => ?_, fun q hq e => ?_, fun r hr a ha e => ?_⟩
  · rw [show yieldA y = core.num.U64.wrapping_add y 3472#u64 from rfl,
      show mcpA t = core.num.U64.wrapping_add t 3440#u64 from rfl, tt_eq_iff (hT y hy) (hT t ht) (by simp) (by simp)] at e
    exact absurd e.2 (by decide)
  · obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
    obtain ⟨-, hvq, hsz⟩ := sc_reply_word hS hq
    have hin : ScObj q nq (scReplyA q) := by have := hsz xq nq hkq; unfold ScObj; rw [hvq]; omega
    have := (hS.scOut q hq xq nq hkq _ hin).2.2.1 y hy
    rw [← e, hv] at this; omega
  · have := hRP.tcb r hr y hy
    have := congrArg UScalar.val e
    rw [hv] at this; omega

/-- A reply word (`RW`) is no `MCP` or `YIELD_TO` word. -/
theorem RW.ne_tcbw {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    (hRP : RPlaced st N T C R c s σ) {b : U64} (hb : RW R C b) {t : U64} (ht : t ∈ T) {K : U64}
    (hK : K.val < 4096) : b ≠ core.num.U64.wrapping_add t K := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hv := tfield_val (hc.tcbs t ht) hK
  rintro e
  rcases hb with ⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩
  · have := hRP.tcb r hr t ht
    have := congrArg UScalar.val e
    rw [rNextA_val (hRP.align r hr), hv] at this; omega
  · obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
    obtain ⟨-, hvq, hsz⟩ := sc_reply_word hS hq
    have hin : ScObj q nq (scReplyA q) := by have := hsz xq nq hkq; unfold ScObj; rw [hvq]; omega
    have := (hS.scOut q hq xq nq hkq _ hin).2.2.1 t ht
    rw [e, hv] at this; omega

/-- **What a `TFoot` step keeps**: the `MCP`, SC `REPLY` and reply link words. -/
theorem TFoot.keep {N T C R : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ)
    (hw : WritesIn st s s' (TFoot st T N C c s σ)) :
    (∀ t ∈ T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧
    (∀ q ∈ C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  refine ⟨fun t ht => hw.mem_eq (mcpA_aligned hT ht) ?_, fun q hq => hw.mem_eq (sc_reply_word hS hq).1 ?_,
    fun r hr => ?_⟩
  · rintro (hb | hb)
    · exact hb.ne_mcp hS ht rfl
    · exact (hb.ne hS hRP).1 t ht rfl
  · rintro (hb | hb)
    · exact hb.ne_screply hS hq rfl
    · exact (hb.ne hS hRP).2.1 q hq rfl
  · have hA := hRP.align r hr
    refine ⟨hw.mem_eq (hRP.aligned hr (Or.inl (rPrevA_val hA))) ?_, hw.mem_eq (hRP.aligned hr (Or.inr (rNextA_val hA))) ?_⟩
    · rintro (hb | hb)
      · exact hb.ne_rword hS hRP hr (Or.inl (rPrevA_val hA)) rfl
      · exact (hb.ne hS hRP).2.2 r hr _ (Or.inl (rPrevA_val hA)) rfl
    · rintro (hb | hb)
      · exact hb.ne_rword hS hRP hr (Or.inr (rNextA_val hA)) rfl
      · exact (hb.ne hS hRP).2.2 r hr _ (Or.inr (rNextA_val hA)) rfl

/-- **What an `RFoot` step keeps**: the `MCP` and `YIELD_TO` words. -/
theorem RFoot.keep {N T C R : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ)
    (hw : WritesIn st s s' (RFoot st T N C R c s σ)) :
    (∀ t ∈ T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ T, L.mem s' (yieldA t) = L.mem s (yieldA t)) := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  refine ⟨fun t ht => hw.mem_eq (mcpA_aligned hT ht) ?_, fun t ht => hw.mem_eq (yieldA_aligned hT ht) ?_⟩
  · rintro (hb | hb)
    · exact hb.ne_mcp hS ht rfl
    · exact hb.ne_tcbw hS hRP ht (K := 3440#u64) (by simp) rfl
  · rintro (hb | hb)
    · exact hb.ne_yield hS ht rfl
    · exact hb.ne_tcbw hS hRP ht (K := 3472#u64) (by simp) rfl

end

end

end Fl4Proofs.P3.Sched
