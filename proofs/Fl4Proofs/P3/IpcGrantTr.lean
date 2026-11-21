/-
P3 (DESIGN.md §9), IPC: **the cap transfer's insert as a trace** (toward
XTopJointSendPushD's `JSendRecvHyp`, the cap grant of a send to a waiting
receiver). FL4's `transfer_caps` inserts at most one cap (the receive slot is
cleared after the insert) and writes only receive-buffer words otherwise; the
send-to-receiver lemmas do that transfer inside the dequeued interval (no
`JAtZ` state), and redo the one insert at the `JAtZ` state before the
dequeue (`JAtZ.insDJ`), whose slots the interval does not touch.

* `patchK`, `capInsert_patch`: the spec's `cap_insert` at a state agreeing
  with another on the two slots' CNodes, the CDT and the original bits gives
  that state with the two CNodes, the CDT and the original bits of the
  other's outcome; `patchK_updK`, `patchK_setUm`.
* `insWords_cong`: two runs of `cdt::insert` from states with the same slot
  words end with the same slot words (Insert's `InsWords`).
* `tc_bodyG`, `transfer_loop_topG`, `transfer_caps_topG`: IpcGrant's loop
  and `transfer_caps` with the insert trace: no insert (`TrN`: the spec state
  the start's up to user memory, the slot words the start's) or one
  (`TrI`/`InsRec`: the facts `JAtZ.insDJ` takes at the start, FL4's insert at
  a state with the start's slot words, the spec's `cap_insert` at the start
  up to user memory), and the writes in slot words and the receiver's buffer
  words (`RFoot`).
-/
import Fl4Proofs.P3.IpcGrantX
import Fl4Proofs.P3.CnodeVsW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec's `cap_insert` at an agreeing state -/

section Patch
open Fl4Spec

/-- `τ` with the objects in `P`, the CDT and the original bits of `σ'`. -/
def patchK (P : ObjRef → Prop) [DecidablePred P] (σ' τ : State Unit) : State Unit :=
  { τ with
    kheap := fun q => if P q then σ'.kheap q else τ.kheap q
    cdt := σ'.cdt
    isOriginalCap := σ'.isOriginalCap }

theorem patchK_kheap (P : ObjRef → Prop) [DecidablePred P] (σ' τ : State Unit) (q : ObjRef) :
    (patchK P σ' τ).kheap q = if P q then σ'.kheap q else τ.kheap q := rfl

theorem patchK_setUm (P : ObjRef → Prop) [DecidablePred P] (σ' τ : State Unit) (um : Word → Word8) :
    patchK P σ' (setUm τ um) = setUm (patchK P σ' τ) um := rfl

theorem patchK_updK {P : ObjRef → Prop} [DecidablePred P] (σ' τ : State Unit) {p : ObjRef} (hp : ¬ P p) (o : KernelObject) :
    patchK P σ' (updK τ p o) = updK (patchK P σ' τ) p o := by
  have hk : (fun q => if P q then σ'.kheap q else Function.update τ.kheap p (some o) q) =
      Function.update (fun q => if P q then σ'.kheap q else τ.kheap q) p (some o) := by
    funext q
    by_cases hq : q = p
    · subst hq; simp [hp]
    · simp [Function.update_of_ne hq]
  unfold patchK updK
  simp only [hk]

theorem getCap_ag {Z : Type} {σ τ : State Z} {p : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool} {a : Cap}
    (hk : σ.kheap p = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (ha : cs idx = some a)
    (ht : τ.kheap p = σ.kheap p) :
    getCap (Z := Z) (p, idx) σ = ({(a, σ)}, False) ∧ getCap (Z := Z) (p, idx) τ = ({(a, τ)}, False) :=
  ⟨getCap_cnode hk hwf ha, getCap_cnode (ht.trans hk) hwf ha⟩

set_option maxHeartbeats 4000000 in
/-- **The spec's `cap_insert` at an agreeing state** (module docstring): both
slots CNode slots, the destination empty. -/
theorem capInsert_patch {σ τ : State Unit} (a : Cap) {srcA : Cap} {ps pd : ObjRef} {is id : List Bool}
    {rs rd : Nat} {css csd : CnodeContents}
    (hks : σ.kheap ps = some (.cnode rs css)) (hwfs : wellFormedCnodeN rs css) (hls : is.length = rs)
    (hsa : css is = some srcA)
    (hkd : σ.kheap pd = some (.cnode rd csd)) (hwfd : wellFormedCnodeN rd csd) (hld : id.length = rd)
    (hda : csd id = some .nullCap) (hne : (ps, is) ≠ (pd, id))
    (hts : τ.kheap ps = σ.kheap ps) (htd : τ.kheap pd = σ.kheap pd) (hc : τ.cdt = σ.cdt)
    (ho : τ.isOriginalCap = σ.isOriginalCap) :
    ∃ σ', capInsert (Z := Unit) a (ps, is) (pd, id) σ = ({((), σ')}, False) ∧
      capInsert (Z := Unit) a (ps, is) (pd, id) τ =
        ({((), patchK (fun q => q = ps ∨ q = pd) σ' τ)}, False) := by
  obtain ⟨gs1, gs2⟩ := getCap_ag hks hwfs hsa hts
  obtain ⟨gd1, gd2⟩ := getCap_ag hkd hwfd hda htd
  -- the two `set_cap`s, at `σ` and at `τ`, by the same CNode values
  have hfin : ∀ (σ1 τ1 : State Unit), σ1.kheap ps = τ1.kheap ps → σ1.kheap pd = τ1.kheap pd →
      (∀ q, q ≠ ps → q ≠ pd → σ1.kheap q = σ.kheap q ∧ τ1.kheap q = τ.kheap q) →
      σ1.cdt = σ.cdt → σ1.isOriginalCap = σ.isOriginalCap → τ1.cdt = τ.cdt → τ1.isOriginalCap = τ.isOriginalCap →
      (∀ σ2 τ2 : State Unit, setCap (Z := Unit) a (pd, id) σ1 = ({((), σ2)}, False) →
        setCap (Z := Unit) a (pd, id) τ1 = ({((), τ2)}, False) →
        σ2.kheap pd = τ2.kheap pd → (∀ q, q ≠ pd → σ2.kheap q = σ1.kheap q ∧ τ2.kheap q = τ1.kheap q) →
        σ2.cdt = σ1.cdt → σ2.isOriginalCap = σ1.isOriginalCap → τ2.cdt = τ1.cdt →
        τ2.isOriginalCap = τ1.isOriginalCap → τ2 = { τ with kheap := τ2.kheap } →
        setUntypedCapAsFull (Z := Unit) srcA a (ps, is) σ = ({((), σ1)}, False) →
        setUntypedCapAsFull (Z := Unit) srcA a (ps, is) τ = ({((), τ1)}, False) →
        ∃ σ', capInsert (Z := Unit) a (ps, is) (pd, id) σ = ({((), σ')}, False) ∧
          capInsert (Z := Unit) a (ps, is) (pd, id) τ =
            ({((), patchK (fun q => q = ps ∨ q = pd) σ' τ)}, False)) := by
    intro σ1 τ1 e1 e2 eo c1 o1 c1' o1' σ2 τ2 h2 h2' f1 fo c2 o2 c2' o2' hτ h1 h1'
    refine ⟨_, capInsert_eq gs1 gd1 h1 h2 (o2.trans o1) (c2.trans c1),
      (capInsert_eq gs2 gd2 h1' h2' (o2'.trans o1') (c2'.trans c1')).trans ?_⟩
    have hK : τ2.kheap = fun q => if q = ps ∨ q = pd then σ2.kheap q else τ.kheap q := by
      funext q
      by_cases q1 : q = pd
      · subst q1; simp [f1]
      by_cases q0 : q = ps
      · subst q0; simp only [true_or, ↓reduceIte]
        rw [(fo q q1).1, (fo q q1).2, e1]
      · simp only [q0, q1, or_self, ↓reduceIte]
        rw [(fo q q1).2, (eo q q0 q1).2]
    rw [hτ]
    unfold capInsertState patchK
    rw [hK, hc, ho]
  by_cases hU : isUntypedCap srcA = true ∧ isUntypedCap a = true ∧ objRefOf srcA = objRefOf a ∧
      capBitsUntyped srcA = capBitsUntyped a
  · -- the source made full
    have s1 := setCap_cnode (Z := Unit) (maxFreeIndexUpdate srcA) hks hwfs hls
    have s1' := setCap_cnode (Z := Unit) (maxFreeIndexUpdate srcA) (hts.trans hks) hwfs hls
    have u1 := (setUntyped_full (σ := σ) (src := (ps, is)) hU).trans s1
    have u1' := (setUntyped_full (σ := τ) (src := (ps, is)) hU).trans s1'
    set cs1 := Function.update css is (some (maxFreeIndexUpdate srcA))
    by_cases hpp : pd = ps
    · subst hpp
      rw [hks] at hkd
      injection hkd with hkd; injection hkd with hr hcs
      subst hr hcs
      have hwf1 := wf_update (maxFreeIndexUpdate srcA) hwfs hls
      have k1 : (setCnodeSlot σ pd rs css is (maxFreeIndexUpdate srcA)).kheap pd = some (.cnode rs cs1) := by
        simp [setCnodeSlot, cs1]
      have k1' : (setCnodeSlot τ pd rs css is (maxFreeIndexUpdate srcA)).kheap pd = some (.cnode rs cs1) := by
        simp [setCnodeSlot, cs1]
      refine hfin (setCnodeSlot σ pd rs css is (maxFreeIndexUpdate srcA))
        (setCnodeSlot τ pd rs css is (maxFreeIndexUpdate srcA)) (by simp [setCnodeSlot]) (by simp [setCnodeSlot])
        (fun q h1 _ => by simp [setCnodeSlot, Function.update_of_ne h1]) rfl rfl rfl rfl _ _
        (setCap_cnode (Z := Unit) a k1 hwf1 hld) (setCap_cnode (Z := Unit) a k1' hwf1 hld)
        (by simp [setCnodeSlot]) (fun q h1 => by simp [setCnodeSlot, Function.update_of_ne h1]) rfl rfl rfl rfl
        rfl u1 u1'
    · have k1 : (setCnodeSlot σ ps rs css is (maxFreeIndexUpdate srcA)).kheap pd = some (.cnode rd csd) := by
        simp [setCnodeSlot, Function.update_of_ne hpp, hkd]
      have k1' : (setCnodeSlot τ ps rs css is (maxFreeIndexUpdate srcA)).kheap pd = some (.cnode rd csd) := by
        simp [setCnodeSlot, Function.update_of_ne hpp, htd, hkd]
      refine hfin (setCnodeSlot σ ps rs css is (maxFreeIndexUpdate srcA))
        (setCnodeSlot τ ps rs css is (maxFreeIndexUpdate srcA)) (by simp [setCnodeSlot])
        (by simp [setCnodeSlot, Function.update_of_ne hpp, htd])
        (fun q h1 _ => by simp [setCnodeSlot, Function.update_of_ne h1]) rfl rfl rfl rfl _ _
        (setCap_cnode (Z := Unit) a k1 hwfd hld) (setCap_cnode (Z := Unit) a k1' hwfd hld)
        (by simp [setCnodeSlot]) (fun q h1 => by simp [setCnodeSlot, Function.update_of_ne h1]) rfl rfl rfl rfl
        rfl u1 u1'
  · -- the source kept
    refine hfin σ τ hts.symm htd.symm (fun q _ _ => ⟨rfl, rfl⟩) rfl rfl rfl rfl _ _
      (setCap_cnode (Z := Unit) a hkd hwfd hld) (setCap_cnode (Z := Unit) a (htd.trans hkd) hwfd hld)
      (by simp [setCnodeSlot]) (fun q h1 => by simp [setCnodeSlot, Function.update_of_ne h1]) rfl rfl rfl rfl
      rfl (setUntyped_skip hU) (setUntyped_skip hU)

theorem patchK_self_of {σ σ' : State Unit} {P : ObjRef → Prop} [DecidablePred P] {m : NonDet (State Unit) Unit}
    (h1 : m σ = ({((), σ')}, False)) (h2 : m σ = ({((), patchK P σ' σ)}, False)) : patchK P σ' σ = σ' := by
  rw [h1] at h2
  have := congrArg Prod.fst h2
  simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
  exact this.symm

end Patch


/-! ## `cdt::insert` from states with the same slots -/

section Cong
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem SlotsSame.wd {m m' : U64 → U64} (h : SlotsSame th m m') {a k : U64} (ha : IsSlot th a) (hk : Off k) :
    m' (wordOf a k) = m (wordOf a k) := by
  obtain ⟨h0, h8, h16, h24⟩ := h a ha
  rcases hk with rfl | rfl | rfl | rfl
  · rw [wordOf_zero]; exact h0
  · exact h8
  · exact h16
  · exact h24

theorem SlotsSame.of_wd {m m' : U64 → U64} (h : ∀ a, IsSlot th a → ∀ k, Off k → m' (wordOf a k) = m (wordOf a k)) :
    SlotsSame th m m' := fun a ha =>
  ⟨by have := h a ha 0#u64 off0; rwa [wordOf_zero] at this, h a ha _ off8, h a ha _ off16, h a ha _ off24⟩

theorem SlotsSame.symm' {m m' : U64 → U64} (h : SlotsSame th m m') : SlotsSame th m' m := fun a ha =>
  let ⟨a1, a2, a3, a4⟩ := h a ha
  ⟨a1.symm, a2.symm, a3.symm, a4.symm⟩

/-- **Two runs of `cdt::insert` from states with the same slot words end with
the same slot words.** -/
theorem insWords_cong {s t s' t' : S} {c srcC : capability.Cap} {src dest : U64}
    (hS : SlotsSame th (L.mem s) (L.mem t)) (hs : IsSlot th src) (hd : IsSlot th dest)
    (h1 : InsWords (L := L) th s s' c srcC src dest) (h2 : InsWords (L := L) th t t' c srcC src dest) :
    SlotsSame th (L.mem s') (L.mem t') := by
  refine SlotsSame.of_wd fun a ha k hk => ?_
  rw [h1 a ha k hk, h2 a ha k hk]
  have e1 := SlotsSame.wd hS hd off24
  have e2 := SlotsSame.wd hS hs off24
  have e3 := SlotsSame.wd hS ha hk
  have e4 : nextOf (L.mem t) src = nextOf (L.mem s) src := by unfold nextOf; rw [e2]
  rw [e4, e1, e2, e3]

end Cong



/-! ## The transfer loop with its insert -/

section LoopG
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **The transfer loop's insert**, recorded against the loop's start
`(s0, σ0)`: FL4's `cdt::insert` of a derived cap `c'` (`CapRel c' a'`) from a
source slot of the extra caps into the receive slot ran at a state `sk` with
`s0`'s slot words (`InsWords` to `sk'`, writing slot words only), the spec's
`cap_insert` at a state `σk` that is `σ0` up to user memory (ending at
`σc`), with the facts `JAtZ.insDJ` takes, at `s0` and `σ0`. -/
def InsRec (th : TypedHeap) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (slots0 : List Fl4Spec.CslotPtr)
    (s0 : S) (σ0 : Fl4Spec.State Unit) (sk' : S) (σc : Fl4Spec.State Unit) : Prop :=
  ∃ (cv c' : capability.Cap) (a' : Fl4Spec.Cap) (ps pd : U64) (rs rd : Nat) (idx idxd : List Bool) (sk : S)
    (σk : Fl4Spec.State Unit),
    th ps = some (.cnode rs) ∧ th pd = some (.cnode rd) ∧ idx.length = rs ∧ idxd.length = rd ∧
    (∃ j, ∃ hj : j < caps.length, (caps[j]).2 = (ps.bv, idx)) ∧ slots0 = [(pd.bv, idxd)] ∧
    capAt (L.mem s0) (cslotAddr (ps.bv, idx)) = ok cv ∧ cv ≠ .Null ∧
    capAt (L.mem s0) (cslotAddr (pd.bv, idxd)) = ok .Null ∧
    CapRel c' a' ∧ CapValid th c' ∧ EncWf c' ∧ c' ≠ .Null ∧ shape c' = shape cv ∧ badgeF c' = badgeF cv ∧
    (isUt cv = true → ¬ ∃ x, σ0.cdt x = some (ps.bv, idx)) ∧ isZb cv = false ∧ okey c' = okey cv ∧
    (∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 cv → Vs.VCapOK P L4 L3 L2 L1 c') ∧
    (Vs.TabUn c' → Vs.TabUn cv) ∧ (isUt cv = true → c' = cv) ∧ (Vs.NativeCap cv → Vs.NativeCap c') ∧
    SlotsSame th (L.mem s0) (L.mem sk) ∧
    InsWords (L := L) th sk sk' c' cv (cslotAddr (ps.bv, idx)) (cslotAddr (pd.bv, idxd)) ∧
    WritesIn st sk sk' (Sched.SlotWd th) ∧
    (∃ um, σk = setUm σ0 um) ∧
    Fl4Spec.capInsert (Z := Unit) a' (ps.bv, idx) (pd.bv, idxd) σk = ({((), σc)}, False)

/-- No insert so far: the spec state is the start's up to user memory, the
slot words are the start's. -/
def TrN (th : TypedHeap) (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  (∃ um, σ = setUm σ0 um) ∧ SlotsSame th (L.mem s0) (L.mem s)

/-- One insert so far (`InsRec`): the spec state is the insert's outcome up
to user memory, the slot words are those right after FL4's insert. -/
def TrI (th : TypedHeap) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (slots0 : List Fl4Spec.CslotPtr)
    (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ sk' σc, InsRec (L := L) th caps slots0 s0 σ0 sk' σc ∧ (∃ um, σ = setUm σc um) ∧
    SlotsSame th (L.mem sk') (L.mem s)

theorem trN_refl {th : TypedHeap} {s0 : S} {σ0 : Fl4Spec.State Unit} : TrN (L := L) th s0 σ0 s0 σ0 :=
  ⟨⟨σ0.machineState.underlyingMemory, rfl⟩, SlotsSame.refl _ _⟩

theorem trN_um {th : TypedHeap} {s0 s s' : S} {σ0 σ : Fl4Spec.State Unit} (h : TrN (L := L) th s0 σ0 s σ)
    (hS : SlotsSame th (L.mem s) (L.mem s')) (v : Fl4Spec.Word → Fl4Spec.Word8) :
    TrN (L := L) th s0 σ0 s' (setUm σ v) := by
  obtain ⟨⟨um, rfl⟩, h0⟩ := h
  exact ⟨⟨v, rfl⟩, SlotsSame.trans' h0 hS⟩

theorem trI_um {th : TypedHeap} {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {slots0 : List Fl4Spec.CslotPtr}
    {s0 s s' : S} {σ0 σ : Fl4Spec.State Unit} (h : TrI (L := L) th caps slots0 s0 σ0 s σ)
    (hS : SlotsSame th (L.mem s) (L.mem s')) (v : Fl4Spec.Word → Fl4Spec.Word8) :
    TrI (L := L) th caps slots0 s0 σ0 s' (setUm σ v) := by
  obtain ⟨sk', σc, hI, ⟨um, rfl⟩, h1⟩ := h
  exact ⟨sk', σc, hI, ⟨v, rfl⟩, SlotsSame.trans' h1 hS⟩

/-- The loop's writes in the receiver's buffer words at `rbw`: slot words
and those buffer words. -/
def RFoot (th : TypedHeap) (rbw b : U64) : Prop := Sched.SlotWd th b ∨ ∃ k : U64, k.val < 128 ∧ b = fl4BufA rbw k

/-- `TInv` with the insert trace and the writes in the receiver's buffer. -/
def TInvG (th : TypedHeap) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ep : U64) (rb : Fl4Spec.Word) (rbw : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (dest0 : U64)
    (slots0 : List Fl4Spec.CslotPtr) (mi0 : Fl4Spec.MessageInfo) (x : S × msginfo.MessageInfo × obj.Slot × U64) :
    Prop :=
  ∃ σ mi slots, x.2.2.2.val ≤ caps.length ∧ MiRel x.2.1 mi ∧ mi.miLength = mi0.miLength ∧
    mi.miLabel = mi0.miLabel ∧
    (∀ r σf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb x.2.2.2.val (caps.drop x.2.2.2.val) slots mi σ =
        ({(r, σf)}, False) →
      Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(r, σf)}, False)) ∧
    IpcRel N T E R B (L.mem x.1) σ ∧ SRE st N T C E R B c x.1 σ ∧ (∃ G, RelTopB (L := L) th G N T C E R B c x.1 σ) ∧
    (∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rb k) σ) ∧
    (∀ j (hj : j < caps.length), x.2.2.2.val ≤ j →
      ∃ cv, capAt (L.mem x.1) (exAt extra j) = ok cv ∧ UwEq ep cv (caps[j]).1) ∧
    ((x.2.2.1 = 0#u64 ∧ slots = []) ∨
      (x.2.2.1 = dest0 ∧ slots = slots0 ∧ dest0 ≠ 0#u64 ∧ SlotsSame th (L.mem s0) (L.mem x.1) ∧ σ.cdt = σ0.cdt)) ∧
    KeepCV σ0 σ ∧ WritesIn st s0 x.1 (FW th B) ∧ x.2.1.caps_unwrapped.val < 8 ∧
    (TrN (L := L) th s0 σ0 x.1 σ ∨ (x.2.2.1 = 0#u64 ∧ TrI (L := L) th caps slots0 s0 σ0 x.1 σ)) ∧
    WritesIn st s0 x.1 (RFoot th rbw)

/-- `TPost` with the insert trace. -/
def TPostG (th : TypedHeap) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (ep : U64) (rb : Fl4Spec.Word)
    (rbw : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (slots0 : List Fl4Spec.CslotPtr) (mi0 : Fl4Spec.MessageInfo)
    (y : S × msginfo.MessageInfo × U64) : Prop :=
  ∃ σ' mf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(mf, σ')}, False) ∧
    MiRel y.2.1 mf ∧ mf.miExtraCaps = BitVec.ofNat 64 y.2.2.val ∧
    y.2.1.caps_unwrapped.val < 8 ∧ y.2.2.val ≤ 3 ∧ mf.miLabel = mi0.miLabel ∧
    IpcRel N T E R B (L.mem y.1) σ' ∧ SRE st N T C E R B c y.1 σ' ∧ (KeepCV σ0 σ' ∧ WritesIn st s0 y.1 (FW th B)) ∧
    (∃ G, RelTopB (L := L) th G N T C E R B c y.1 σ') ∧
    (TrN (L := L) th s0 σ0 y.1 σ' ∨ TrI (L := L) th caps slots0 s0 σ0 y.1 σ') ∧
    WritesIn st s0 y.1 (RFoot th rbw)

theorem tpostG_of {th : TypedHeap} {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {ep : U64} {rb : Fl4Spec.Word}
    {σ0 σ : Fl4Spec.State Unit} {slots0 slots : List Fl4Spec.CslotPtr} {mi0 mi : Fl4Spec.MessageInfo} {s : S}
    {out : msginfo.MessageInfo} {i : U64}
    (hmi : MiRel out mi)
    (hch : ∀ r σf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb i.val (caps.drop i.val) slots mi σ =
        ({(r, σf)}, False) →
      Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(r, σf)}, False))
    (hend : Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb i.val (caps.drop i.val) slots mi σ =
      ({(miAt mi i.val, σ)}, False))
    (hcu : out.caps_unwrapped.val < 8) (hi3 : i.val ≤ 3) (hlb : mi.miLabel = mi0.miLabel)
    (hR : IpcRel N T E R B (L.mem s) σ) (hS : SRE st N T C E R B c s σ) {s0 : S} (hK : KeepCV σ0 σ)
    (hW : WritesIn st s0 s (FW th B))
    (hB : ∃ G, RelTopB (L := L) th G N T C E R B c s σ)
    (htr : TrN (L := L) th s0 σ0 s σ ∨ TrI (L := L) th caps slots0 s0 σ0 s σ) {rbw : U64}
    (hWr : WritesIn st s0 s (RFoot th rbw)) :
    TPostG (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps ep rb rbw s0 σ0
      slots0 mi0 (s, out, i) :=
  ⟨σ, miAt mi i.val, hch _ _ hend, hmi, rfl, hcu, hi3, hlb, hR, hS, ⟨hK, hW⟩, hB, htr, hWr⟩

set_option maxHeartbeats 8000000 in
/-- **One step of the transfer loop**, with the insert trace (IpcGrant's `tc_body`). -/
theorem tc_bodyG (hP0 : IPlaced N T E R B) {th : TypedHeap} {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rbw : U64} {rb : Fl4Spec.Word} {s0 : S}
    {σ0 : Fl4Spec.State Unit} {dest0 : U64} {slots0 : List Fl4Spec.CslotPtr} {mi0 : Fl4Spec.MessageInfo}
    (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK th (L.mem s0) (exAt extra j) caps[j])
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (hdest : dest0 ≠ 0#u64 → ∃ d, slots0 = [d] ∧ DestOK th (L.mem s0) dest0 d)
    (hm : BufMap B rbw rb) (x : S × msginfo.MessageInfo × obj.Slot × U64)
    (hx : TInvG (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps extra ep rb
      rbw s0 σ0 dest0 slots0 mi0 x) :
    ipc.transfer_caps_loop.body st extra ep rbw x.1 x.2.1 x.2.2.1 x.2.2.2 ⦃ r => match r with
      | .done y => TPostG (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps ep
          rb rbw s0 σ0 slots0 mi0 y
      | .cont x' => TInvG (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps
          extra ep rb rbw s0 σ0 dest0 slots0 mi0 x' ∧ 3 - x'.2.2.2.val < 3 - x.2.2.2.val ⦄ := by
  obtain ⟨s, out, dest, i⟩ := x
  obtain ⟨σ, mi, slots, hi, hmi, hml, hmlb, hch, hR, hS, ⟨G, hB⟩, hu, hpend, hdst, hK0, hW0, hcu, hTr, hWr⟩ := hx
  dsimp only at hi hmi hch hR hS hB hpend hdst hTr ⊢
  have hPl : Placed th := hB.1
  unfold ipc.transfer_caps_loop.body
  by_cases h3 : i < 3#u64
  · have hi3 : i.val < 3 := by scalar_tac
    rw [if_pos h3]
    simp only [lift, bind_ok]
    rw [index_exAt extra _ (by rw [cast_us_val i hi3]; exact hi3), cast_us_val i hi3]
    simp only [bind_ok, obj.Slot.is_null]
    by_cases hlt : i.val < caps.length
    · obtain ⟨ps, rs, idx, cv0, hps, hls, hsl, hxa, hcv0, habs0, hw0, he0, hcvv0⟩ := hsrc i.val hlt
      have hsI : IsSlot th (exAt extra i.val) := by
        rw [hxa]; exact AbsSlot.isSlot (⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩ : AbsSlot th (ps.bv, idx))
      have hne : exAt extra i.val ≠ 0#u64 := hsI.ne_zero hPl
      simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨cv, hcv, huw⟩ := hpend i.val hlt le_rfl
      rw [slot_cap_eq, hcv]
      simp only [bind_ok]
      rw [unwrap_eq]
      simp only [bind_ok]
      have hdrop : caps.drop i.val = caps[i.val] :: caps.drop (i.val + 1) := List.drop_eq_getElem_cons hlt
      by_cases hu' : UnwrapP ep (absCap cv)
      · rw [if_pos hu']
        simp only [buf_caps_eq, bind_ok]
        have hk : (core.num.U64.wrapping_add 122#u64 i).val = 122 + i.val := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        refine WP.spec_bind (buf_set_top hP0 hB hR hS hm (k := core.num.U64.wrapping_add 122#u64 i)
          (by rw [hk]; omega) (epBadgeW cv) (hu _ (by rw [hk]; omega))) ?_
        rintro s2 ⟨rfl, hst, hR2, hS2, hB2⟩
        try simp only [lift, bind_ok]
        have hand : (i &&& 63#u64).val = i.val := by
          rw [UScalar.val_and]
          have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
          rcases this with h | h | h <;> rw [h] <;> rfl
        obtain ⟨i6, h6e, h6v, h6⟩ := spec_exists (U64.ShiftLeft_spec 1#u64 (i &&& 63#u64) (by rw [hand]; omega))
        have hi6 : i6.val < 8 := by
          rw [h6v, hand]
          rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with h | h | h <;> rw [h] <;>
            simp [U64.size, U64.numBits]
        rw [h6e]
        simp only [bind_ok]
        obtain ⟨i8, h8e, h8⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        rw [h8e, bind_ok, WP.spec_ok]
        have hi8 : i8.val = i.val + 1 := by simpa using h8
        set σ1 := setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr rb (core.num.U64.wrapping_add 122#u64 i).val)
          (epBadgeW cv).bv) with hσ1
        have hwp := hm _ (by rw [hk]; omega : (core.num.U64.wrapping_add 122#u64 i).val < 128)
        have hal := (hP0.e.balign _ hwp).1
        have hSS : SlotsSame th (L.mem s) (L.mem (L.wr s (fl4BufA rbw (core.num.U64.wrapping_add 122#u64 i))
            (epBadgeW cv))) :=
          slotsSame_wr hPl s _ hal fun a ha h => hB.2.2.2.2.2.1.slot _
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hwp, le_refl _, by omega⟩)))) a ha h
        refine ⟨⟨σ1, miUnwrap mi i.val, slots, by rw [hi8]; omega, ⟨hmi.1, ?_, hmi.2.2⟩, hml, hmlb, ?_, hR2, hS2,
          ⟨G, hB2⟩, fun k hk => (inUserFrame_setUm _ _ _).2 (hu k hk), fun j hj hij => ?_, ?_, ⟨fun p => hK0.1 p, hK0.2⟩,
          (hW0.trans (writesIn_wr hal)).mono fun b h => h.elim id (fun e => Or.inr ⟨_, hwp, e⟩),
          by show (out.caps_unwrapped ||| i6).val < 2 ^ 3; rw [UScalar.val_or]; exact Nat.or_lt_two_pow hcu hi6,
          hTr.imp (fun h => trN_um h hSS _) (fun h => ⟨h.1, trI_um h.2 hSS _⟩),
          (hWr.trans (writesIn_wr hal)).mono fun b h => h.elim id (fun e => Or.inr ⟨_, by rw [hk]; omega, e⟩)⟩,
          by rw [hi8]; omega⟩
        · show (out.caps_unwrapped ||| i6).bv = mi.miCapsUnwrapped ||| ((1 : Fl4Spec.Data) <<< i.val)
          rw [UScalar.bv_or, h6, hand]; exact congrArg₂ (· ||| ·) hmi.2.1 rfl
        · intro r σf hr
          refine hch r σf ?_
          rw [hdrop]
          refine tcl_badge (hc := huw.1.mp hu') ?_
            (by rw [hi8] at hr; exact hr)
          unfold Fl4Spec.setExtraBadge
          show Fl4Spec.storeWordOffs rb (Fl4Spec.bufferCptrIndex + i.val) (Fl4Spec.capEpBadge (caps[i.val]).1) σ = _
          rw [← huw.2 (huw.1.mp hu')]
          rw [show Fl4Spec.bufferCptrIndex + i.val = (core.num.U64.wrapping_add 122#u64 i).val by
            rw [hk]; rfl]
          exact hst
        · obtain ⟨cv', h1, h2⟩ := hpend j hj (by rw [hi8] at hij; omega)
          exact ⟨cv', by rw [hSS.capAt (by
            obtain ⟨ps', rs', idx', cv'', hps', hls', -, hxa', -⟩ := hsrc j hj
            rw [hxa']; exact AbsSlot.isSlot (⟨ps', rfl, Or.inl (by simpa [hls'] using hps')⟩ :
              AbsSlot th (ps'.bv, idx')))]; exact h1, h2⟩
        · rcases hdst with h | ⟨h1, h2, h3', h4, h5⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, h2, h3', SlotsSame.trans' h4 hSS, h5⟩
      · rw [if_neg hu']
        simp only []
        rcases hdst with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hd0, hSS, hcdt⟩
        · simp only [decide_true, ↓reduceIte, WP.spec_ok]
          refine tpostG_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩ (hTr.imp_right And.right) hWr
          rw [hdrop]
          exact tcl_noslot (fun h => hu' (huw.1.mpr h))
        · obtain ⟨d, hsl0, ⟨pd, rd, idxd, hpd, hld, rfl, hdA, hdN⟩⟩ := hdest hd0
          subst hsl0
          simp only [hd0, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hcvs : capAt (L.mem s) (exAt extra i.val) = ok cv0 := by rw [hSS.capAt hsI, hcv0]
          rw [hcv] at hcvs
          have hcvs' : cv = cv0 := by simpa using hcvs
          subst hcvs'
          have hsl' : (caps[i.val]).2 = (ps.bv, idx) := hsl
          have hnot : ¬ UnwrapP ep (caps[i.val]).1 := fun h => hu' (huw.1.mpr h)
          have hAs : AbsSlot th (ps.bv, idx) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
          have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
          have hdI : IsSlot th dest := by rw [hdA]; exact hAd.isSlot
          have hncs : cv ≠ .Null → NoChildrenRel (st := st) s σ (exAt extra i.val) (caps[i.val]).2 := by
            intro hut
            obtain ⟨-, ⟨-, -, hM, hC, hI⟩, -⟩ := hB
            rw [hsl', hxa]
            refine noChildren_of_adj th hPl s σ G hM hC (hI.parentAdj (th := th)) _ hAs
              ((hM.members _).2 ⟨hAs.isSlot, cv, by rw [← hxa]; exact hcv, ?_⟩)
            exact hut
          obtain ⟨r, hr, r', hr', hdr⟩ := derive_rel (Z := Unit) s σ (exAt extra i.val) (caps[i.val]).2 cv hw0 he0
            (fun h => hncs (by rintro rfl; exact h))
          rw [← habs0] at hr'
          rw [hr]
          simp only [bind_ok]
          cases r with
          | Err e =>
            cases r' with
            | ok _ => exact hdr.elim
            | error e' =>
              simp only [WP.spec_ok]
              refine tpostG_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩ (hTr.imp_right And.right) hWr
              rw [hdrop]
              exact tcl_derr hnot hr'
          | Ok c' =>
            cases r' with
            | error _ => exact hdr.elim
            | ok a' =>
              obtain ⟨hw', ha', he', hv', hk'⟩ := hdr
              simp only []
              by_cases hn : c' = .Null
              · subst hn
                rw [cap_is_null_null]
                simp only [bind_ok, ↓reduceIte, WP.spec_ok]
                refine tpostG_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩ (hTr.imp_right And.right) hWr
                rw [hdrop]
                rw [← ha'] at hr'
                exact tcl_dnull hnot hr'
              · rw [cap_is_null_ne hn]
                simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
                have hcvn : cv ≠ .Null := by
                  rintro rfl; unfold objects.derive_cap at hr; simp at hr; exact hn hr.symm
                obtain ⟨hsh, hbd, hzb, hnu⟩ := derive_shape hr hn (hncs hcvn)
                have hsnn : cv ≠ .Null := fun h => hn ((Vs.shape_kind hsh).2.2.2.2.2 h)
                have hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idx)) = ok cv := by rw [← hxa]; exact hcv
                have hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null := by
                  rw [← hdA, hSS.capAt hdI]; exact hdN
                have hut : isUt cv = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idx)) := by
                  intro hu0 y hy
                  obtain ⟨z, hz⟩ := desc_tail_child hy
                  exact hnu hu0 (by rw [hsl']; exact (hB.2.1.2.2.2.1.has_child_iff hPl hAs).2 ⟨z, hz⟩)
                have hsI' : IsSlot th (cslotAddr (ps.bv, idx)) := hAs.isSlot
                have hnx : nextOf (L.mem s) (cslotAddr (ps.bv, idx)) = 0#u64 ∨
                    IsSlot th (nextOf (L.mem s) (cslotAddr (ps.bv, idx))) := by
                  have hm := (hB.2.1.2.2.1.members _).2 ⟨hsI', cv, hsrcC, hsnn⟩
                  rcases hB.2.1.2.2.1.next_mem hm with h | ⟨h, -⟩
                  · exact Or.inl h
                  · exact Or.inr ((hB.2.1.2.2.1.members _).1 h).1
                have hdnm : cslotAddr (pd.bv, idxd) ∉ G.chains.flatten := fun h => by
                  obtain ⟨-, c0, h0, hn0⟩ := (hB.2.1.2.2.1.members _).1 h
                  rw [hdst] at h0; exact hn0 (eq_of_ok_eq h0).symm
                have hsd : cslotAddr (ps.bv, idx) ≠ cslotAddr (pd.bv, idxd) := fun e => by
                  rw [e, hdst] at hsrcC; exact hsnn (eq_of_ok_eq hsrcC).symm
                have hnxS : nextOf (L.mem s) (cslotAddr (ps.bv, idx)) = 0#u64 ∨
                    (IsSlot th (nextOf (L.mem s) (cslotAddr (ps.bv, idx))) ∧
                      nextOf (L.mem s) (cslotAddr (ps.bv, idx)) ≠ cslotAddr (pd.bv, idxd) ∧
                      nextOf (L.mem s) (cslotAddr (ps.bv, idx)) ≠ cslotAddr (ps.bv, idx)) := by
                  have hm := (hB.2.1.2.2.1.members _).2 ⟨hsI', cv, hsrcC, hsnn⟩
                  rcases hB.2.1.2.2.1.next_mem hm with h | ⟨h1, h2⟩
                  · exact Or.inl h
                  · exact Or.inr ⟨((hB.2.1.2.2.1.members _).1 h1).1, fun e => hdnm (e ▸ h1), h2⟩
                have hins0 := WP.spec_and (insert_top hP0 hB hR hS hps hpd hls hld hsrcC hsnn hdst c' a' ⟨hw', ha'⟩
                  (hv' th hcvv0) he' hn hsh (Or.inl hbd) hut hzb (derive_okey hr hn)
                  (fun P L4 L3 L2 L1 => derive_vcap hr P L4 L3 L2 L1) (derive_ut hr))
                  (insert_capfr2 hPl s c' _ _ hsI' hAd.isSlot cv hsrcC he0 he' hnx)
                have hins := WP.spec_and hins0 (insert_mem hPl s c' _ _ hsI' hAd.isSlot hsd cv hsrcC hnxS)
                rw [← hxa, ← hdA] at hins
                refine WP.spec_bind hins ?_
                rintro s2 ⟨⟨⟨σ2, hci, hR2, hS2, ⟨hW2, hK2⟩, G2, hB2⟩, hfr⟩, hiw⟩
                rw [hxa, hdA] at hiw
                obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
                rw [h3e, bind_ok, WP.spec_ok]
                have hi3v : i3.val = i.val + 1 := by simpa using h3v
                have hmem : ((), σ2) ∈ (Fl4Spec.capInsert (Z := Unit) a' (ps.bv, idx) (pd.bv, idxd) σ).1 := by
                  rw [hci]; rfl
                have hK := capInsert_nkn a' _ _ σ _ hmem
                have hrec : InsRec (L := L) th caps [(pd.bv, idxd)] s0 σ0 s2 σ2 := by
                  obtain ⟨⟨um, hum⟩, -⟩ := hTr.resolve_right fun h => hd0 h.1
                  exact ⟨cv, c', a', ps, pd, rs, rd, idx, idxd, s, σ, hps, hpd, hls, hld, ⟨i.val, hlt, hsl'⟩, rfl,
                    by rw [← hxa]; exact hcv0, hsnn, by rw [← hdA]; exact hdN, ⟨hw', ha'⟩, hv' th hcvv0, he', hn,
                    hsh, hbd, fun hu0 hx => hnu hu0 (by rw [hcdt, hsl']; exact hx), hzb, derive_okey hr hn,
                    fun P L4 L3 L2 L1 => derive_vcap hr P L4 L3 L2 L1, fun h => (derive_tabun hr h).elim, derive_ut hr, derive_nat hr, hSS,
                    hiw, hW2, ⟨um, hum⟩, hci⟩
                refine ⟨⟨σ2, mi, [], by rw [hi3v]; omega, hmi, hml, hmlb, fun r σf hr0 => ?_, hR2, hS2, ⟨G2, hB2⟩,
                  fun k hk => hK.inUserFrame (hu k hk), fun j hj hij => ?_, Or.inl ⟨rfl, rfl⟩, hK0.trans hK2,
                  (hW0.trans hW2).mono fun b h => h.elim id Or.inl, hcu, Or.inr ⟨rfl, s2, σ2, hrec,
                    ⟨σ2.machineState.underlyingMemory, rfl⟩, SlotsSame.refl _ _⟩,
                  (hWr.trans hW2).mono fun b h => h.elim id Or.inl⟩, by rw [hi3v]; omega⟩
                · refine hch r σf ?_
                  rw [hdrop]
                  refine tcl_insert hnot hr' (fun h => hn ((CapRel.null_iff ⟨hw', ha'⟩).1 h)) ?_
                    (by rw [hi3v] at hr0; exact hr0)
                  show Fl4Spec.capInsert a' (caps[i.val]).2 (pd.bv, idxd) σ = _
                  rw [hsl']; exact hci
                · obtain ⟨cv', h1, h2⟩ := hpend j hj (by rw [hi3v] at hij; omega)
                  obtain ⟨ps', rs', idx', cv'', hps', hls', -, hxa', -⟩ := hsrc j hj
                  have hjI : IsSlot th (exAt extra j) := by
                    rw [hxa']; exact AbsSlot.isSlot (⟨ps', rfl, Or.inl (by simpa [hls'] using hps')⟩ :
                      AbsSlot th (ps'.bv, idx'))
                  obtain ⟨-, -, -, cvj, -, -, -, -, hcvj, habsj, -⟩ := hsrc j hj
                  have hsrcfull : ∀ c'', fullF cv c' = some c'' → ¬ UnwrapP ep (absCap cv) := fun c'' hf =>
                    not_unwrap_of_ut (by
                      cases cv <;> simp [fullF] at hf
                      exact ⟨_, _, _, _, rfl⟩)
                  by_cases ejd : exAt extra j = dest
                  · refine ⟨c', by rw [ejd]; exact hfr.2.1, ?_, fun h => ?_⟩
                    · rw [ejd, hdN] at hcvj
                      have : cvj = .Null := by simpa using hcvj.symm
                      rw [habsj, this]
                      refine ⟨fun h => absurd ((unwrap_shape ep cv).2 (hsh ▸ (unwrap_shape ep c').1 h)) hu',
                        fun h => absurd h not_unwrap_of_null⟩
                    · rw [ejd, hdN] at hcvj
                      have : cvj = .Null := by simpa using hcvj.symm
                      rw [habsj, this] at h; exact absurd h not_unwrap_of_null
                  · rcases hfr.2.2 _ hjI ejd with heq | ⟨ejs, c'', hfc, hc''⟩
                    · exact ⟨cv', by rw [heq]; exact h1, h2⟩
                    · rw [ejs, hcv0] at hcvj
                      have : cvj = cv := by simpa using hcvj.symm
                      have hnu := hsrcfull c'' hfc
                      have hnu'' := not_unwrap_of_ut (ep := ep) (fullF_ut hfc)
                      refine ⟨c'', hc'', ⟨fun h => absurd h hnu'', fun h => ?_⟩, fun h => ?_⟩
                      · rw [habsj, this] at h; exact absurd h hnu
                      · rw [habsj, this] at h; exact absurd h hnu
    · have hieq : i.val = caps.length := by omega
      rw [hnull i.val (by omega) hi3]
      simp only [decide_true, ↓reduceIte, WP.spec_ok]
      refine tpostG_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩ (hTr.imp_right And.right) hWr
      rw [hieq, List.drop_length, ← hieq]
      exact tcl_nil _ _ _
  · rw [if_neg h3]
    simp only [WP.spec_ok]
    have hieq : i.val = caps.length := by
      have : 3 ≤ i.val := by scalar_tac
      omega
    refine tpostG_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩ (hTr.imp_right And.right) hWr
    rw [hieq, List.drop_length, ← hieq]
    exact tcl_nil _ _ _

/-- IpcGrant's `transfer_loop_top` with the insert trace. -/
theorem transfer_loop_topG (hP0 : IPlaced N T E R B) {th : TypedHeap} {G : MdbGhost}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rbw : U64}
    {rb : Fl4Spec.Word} {s0 : S} {σ0 : Fl4Spec.State Unit} {dest0 : U64} {slots0 : List Fl4Spec.CslotPtr}
    {mi0 : Fl4Spec.MessageInfo} (out0 : msginfo.MessageInfo) (hmi0 : MiRel out0 mi0)
    (hcu0 : out0.caps_unwrapped.val < 8) (hB0 : RelTopB (L := L) th G N T C E R B c s0 σ0) (hR0 : IpcRel N T E R B (L.mem s0) σ0)
    (hS0 : SRE st N T C E R B c s0 σ0) (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK th (L.mem s0) (exAt extra j) caps[j])
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (hD : DestConf th (L.mem s0) caps extra dest0 slots0)
    (hm : BufMap B rbw rb) (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rb k) σ0) :
    ipc.transfer_caps_loop st s0 extra ep rbw out0 dest0 0#u64 ⦃ y =>
      TPostG (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps ep rb rbw
        s0 σ0 slots0 mi0 y ⦄ := by
  have hdest : dest0 ≠ 0#u64 → ∃ d, slots0 = [d] ∧ DestOK th (L.mem s0) dest0 d := fun h => by
    rcases hD with ⟨h0, -⟩ | ⟨-, hd⟩
    · exact absurd h0 h
    · exact hd
  unfold ipc.transfer_caps_loop
  refine loop.spec_decr_nat (fun x => 3 - x.2.2.2.val)
    (TInvG (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps extra ep rb
      rbw s0 σ0 dest0 slots0 mi0) _ _ _ (fun x hx => ?_) ?_
  · obtain ⟨s, o, d, i⟩ := x
    have h := tc_bodyG hP0 hlen hsrc hnull hdest hm (s, o, d, i) hx
    refine WP.spec_mono h ?_
    intro r hr
    cases r with
    | done y => exact hr
    | cont x' => exact hr
  · refine ⟨σ0, mi0, slots0, by simp, hmi0, rfl, rfl, fun r σf h => by simpa using h, hR0, hS0, ⟨G, hB0⟩, hu,
      fun j hj _ => ?_, ?_, KeepCV.refl σ0, WritesIn.refl s0 _, hcu0,
      Or.inl ⟨⟨σ0.machineState.underlyingMemory, rfl⟩, SlotsSame.refl _ _⟩, WritesIn.refl s0 _⟩
    · obtain ⟨ps, rs, idx, cv, -, -, -, -, hcv, habs, -⟩ := hsrc j hj
      exact ⟨cv, hcv, UwEq.of_abs habs.symm⟩
    · rcases hD with ⟨h0, h1⟩ | ⟨h0, -⟩
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨rfl, rfl, h0, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

set_option maxHeartbeats 4000000 in
/-- IpcGrant's `transfer_caps_top` with the insert trace. -/
theorem transfer_caps_topG (hP0 : IPlaced N T E R B) {th : TypedHeap} {G : MdbGhost} {s : S}
    {σ : Fl4Spec.State Unit} (hB : RelTopB (L := L) th G N T C E R B c s σ) (hR : IpcRel N T E R B (L.mem s) σ)
    (hS : SRE st N T C E R B c s σ) (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo)
    (hil : info.length.bv = mi.miLength) (hlb : info.label.bv = mi.miLabel)
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK th (L.mem s) (exAt extra j) caps[j])
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (ep : U64) (receiver : obj.Tcb) (rbw : U64) (rbo : Option Fl4Spec.Word) (hrb : rbw = 0#u64 ↔ rbo = none)
    (hm : ∀ rb, rbo = some rb → BufMap B rbw rb ∧ ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rb k) σ)
    (hGRs : ∀ rb, rbo = some rb → ∃ sl, Fl4Spec.getReceiveSlots (Z := Unit) receiver.bv (some rb) σ = ({(sl, σ)}, False))
    (hG1 : ∀ rb, rbo = some rb → ipc.get_receive_slot st s receiver rbw ⦃ dest => ∃ slots,
      Fl4Spec.getReceiveSlots (Z := Unit) receiver.bv (some rb) σ = ({(slots, σ)}, False) ∧
      DestConf th (L.mem s) caps extra dest slots ⦄)
    (hGL : ∀ rb, rbo = some rb → ipc.get_receive_slot st s receiver rbw ⦃ dest => dest ≠ 0#u64 → ∃ pd idx,
      dest = cslotAddr (pd.bv, idx) ∧ th pd = some (.cnode idx.length) ∧ DestCap th (L.mem s) pd ⦄) :
    ipc.transfer_caps st s info extra ep receiver rbw ⦃ r => ∃ σ' mf,
      Fl4Spec.transferCaps (Z := Unit) mi caps (some ep.bv) receiver.bv rbo σ = ({(mf, σ')}, False) ∧
      MiRel r.1 mf ∧ r.1.extra_caps.bv = mf.miExtraCaps ∧ IpcRel N T E R B (L.mem r.2) σ' ∧
      r.1.caps_unwrapped.val < 8 ∧ r.1.extra_caps.val ≤ 3 ∧ mf.miLabel = mi.miLabel ∧
      SRE st N T C E R B c r.2 σ' ∧ (KeepCV σ σ' ∧ WritesIn st s r.2 (FW th B)) ∧
      (∃ G', RelTopB (L := L) th G' N T C E R B c r.2 σ') ∧
      (TrN (L := L) th s σ r.2 σ' ∨ ∃ rb slots, rbo = some rb ∧
        Fl4Spec.getReceiveSlots (Z := Unit) receiver.bv (some rb) σ = ({(slots, σ)}, False) ∧
        TrI (L := L) th caps slots s σ r.2 σ' ∧
        ∀ d ∈ slots, ∃ pd, d.1 = pd.bv ∧ DestCap th (L.mem s) pd) ∧
      WritesIn st s r.2 (RFoot th rbw) ⦄ := by
  have hmi0 : MiRel { label := info.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := info.length }
      ⟨mi.miLength, 0, 0, mi.miLabel⟩ := ⟨hil, rfl, hlb⟩
  -- the spec without caps or without a receive buffer
  have hnone : rbo = none → Fl4Spec.transferCaps (Z := Unit) mi caps (some ep.bv) receiver.bv rbo σ =
      ({(⟨mi.miLength, 0, 0, mi.miLabel⟩, σ)}, False) := by
    rintro rfl
    unfold Fl4Spec.transferCaps
    rw [nd_bind_one (show Fl4Spec.getReceiveSlots (Z := Unit) receiver.bv none σ = ({([], σ)}, False) from rfl),
      nd_pure_bind']
    rfl
  have hnil : caps = [] → ∀ rb, rbo = some rb → Fl4Spec.transferCaps (Z := Unit) mi caps (some ep.bv) receiver.bv rbo σ =
      ({(⟨mi.miLength, 0, 0, mi.miLabel⟩, σ)}, False) := by
    rintro rfl rb rfl
    obtain ⟨sl, hsl⟩ := hGRs rb rfl
    unfold Fl4Spec.transferCaps
    rw [nd_bind_one hsl, nd_pure_bind']
    exact tcl_nil _ _ _
  unfold ipc.transfer_caps msginfo.MessageInfo.new
  simp only [bind_ok]
  rw [index_exAt extra 0#usize (by decide), show ((0#usize : Usize).val) = 0 from rfl]
  simp only [bind_ok, obj.Slot.is_null]
  by_cases h0 : exAt extra 0 = 0#u64
  · have hcn : caps = [] := by
      cases caps with
      | nil => rfl
      | cons y ys =>
        exfalso
        obtain ⟨ps, rs, idx, cv, hps, hls, -, hxa, -⟩ := hsrc 0 (by simp)
        have := (AbsSlot.isSlot (⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩ : AbsSlot th (ps.bv, idx))).ne_zero hB.1
        rw [← hxa] at this; exact this h0
    rw [decide_eq_true h0, if_pos rfl, WP.spec_ok]
    refine ⟨σ, ⟨mi.miLength, 0, 0, mi.miLabel⟩, ?_, hmi0, rfl, hR, by simp, by simp, rfl, hS,
      ⟨KeepCV.refl σ, WritesIn.refl s _⟩, ⟨G, hB⟩, Or.inl trN_refl, WritesIn.refl s _⟩
    cases e : rbo with
    | none => rw [← e]; exact hnone e
    | some rb => rw [← e]; exact hnil hcn rb e
  · rw [decide_eq_false h0, if_neg Bool.false_ne_true]
    by_cases hr0 : rbw = 0#u64
    · rw [if_pos hr0, WP.spec_ok]
      exact ⟨σ, _, hnone (hrb.1 hr0), hmi0, rfl, hR, by simp, by simp, rfl, hS, ⟨KeepCV.refl σ, WritesIn.refl s _⟩,
        ⟨G, hB⟩, Or.inl trN_refl, WritesIn.refl s _⟩
    · rw [if_neg hr0]
      obtain ⟨rb, hrbo⟩ : ∃ rb, rbo = some rb := by
        cases e : rbo with
        | none => exact absurd (hrb.2 e) hr0
        | some rb => exact ⟨rb, rfl⟩
      obtain ⟨hmb, hu⟩ := hm rb hrbo
      refine WP.spec_bind (WP.spec_and (hG1 rb hrbo) (hGL rb hrbo)) ?_
      rintro dest ⟨⟨slots, hsl, hD⟩, hL⟩
      have hDL : ∀ d ∈ slots, ∃ pd, d.1 = pd.bv ∧ DestCap th (L.mem s) pd := by
        intro d hd
        rcases hD with ⟨-, rfl⟩ | ⟨h0, d', rfl, hok⟩
        · simp at hd
        obtain rfl := List.mem_singleton.1 hd
        obtain ⟨pd, idx, he, hpd, hL'⟩ := hL h0
        obtain ⟨pd0, rd0, idx0, hpd0, hl0, rfl, he0, -⟩ := hok
        have e := cslotAddr_inj hB.1 (⟨pd0, rfl, Or.inl (by rw [hl0]; exact hpd0)⟩ : AbsSlot th (pd0.bv, idx0))
          (⟨pd, rfl, Or.inl hpd⟩ : AbsSlot th (pd.bv, idx)) (he0.symm.trans he)
        exact ⟨pd, congrArg Prod.fst e, hL'⟩
      refine WP.spec_bind (transfer_loop_topG hP0 _ hmi0 (by simp) hB hR hS hlen hsrc hnull hD hmb hu) ?_
      rintro ⟨s2, out1, i⟩ ⟨σ', mf, hloop, hmi1, hex, hcu1, hi31, hlb1, hR', hS', hF', hB', htr, hWr⟩
      refine (WP.spec_ok _).2 ⟨σ', mf, ?_, hmi1, ?_, hR', hcu1, hi31, hlb1, hS', hF', hB',
        htr.imp_right fun h => ⟨rb, slots, hrbo, hsl, h, hDL⟩, hWr⟩
      swap
      · show i.bv = mf.miExtraCaps
        rw [hex]; apply BitVec.eq_of_toNat_eq
        show i.val = (BitVec.ofNat 64 i.val).toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by scalar_tac)]
      subst hrbo
      unfold Fl4Spec.transferCaps
      rw [nd_bind_one hsl, nd_pure_bind']
      exact hloop

end LoopG

end

end Fl4Proofs.P3.Ipc
