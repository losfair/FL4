/-
P3 (DESIGN.md §9), scheduler: **`JAtZ` across FL4's TCB timers** (`timer::fire`,
l4h 0003; toward `jat_scheduleT`'s `hfireJ`).

`timer::fire`'s loop body takes the current core's earliest due timer `t`
out of the timer tree (`timer::remove`), signals `t`'s bound notification,
if any (`send_signal`), and sets the core's `REPROGRAM` word. The spec sees
one `Fire`: the signal (`Signal`), then `reprogram_timer` set.

* `JAtZ.tmw_word`, `JAtZ.tmw_obj`: a timer word (`TmW`: the TCBs' timer
  fields, every core's timer-tree words, core `c`'s `REPROGRAM`) lies in no
  object of `H` but a TCB's timer fields (`HeapOK`, `JKern.hnd`).
* `JAtZ.tmw_step`: writes of timer words, `REPROGRAM` kept or set to 1,
  keep `JAtZ` at the same sets, the spec's `reprogram_timer` or'ed with
  whether it was set (`XTopAt.tmStep`; the other fields from the words kept
  and the spec's frame `NFr` with only the flag changed).
* `SignalJHyp` [J]: `send_signal` from `JAtZ` at a notification of `N`
  keeps `JAtZ` (at fresh VSpace sets) and the domain time, against the
  spec's `send_signal` (the one step of the loop not proved here; ScSignalJ
  proves it but for the waking branches, `signalJHyp_of`).
* `JAtZ.fireJ`: the loop (`timer.fire_loop`), from `JAtZ` to `JAtZ` after
  `Fires`, the domain time kept.
* `jat_scheduleF`: `jat_scheduleT2` with `hfireJ` discharged by `fireJ`
  (given `SignalJHyp`), at fresh VSpace sets.
-/
import Fl4Proofs.P3.XTopJointFin
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- `Inv` reads no timer flag. -/
theorem Sched.Inv.rt {σ : State Unit} (h : Inv σ) (v : Bool) : Inv { σ with reprogramTimer := v } := by
  exact h.congr rfl rfl rfl rfl

/-- The spec's frame of a timer-flag change (`NFr` with nothing else changed). -/
theorem Sched.NFr.rt (r : ObjRef) (σ : State Unit) (v : Bool) : NFr true r σ { σ with reprogramTimer := v } :=
  NFr.ofSk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ => ⟨rfl, rfl⟩) rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A timer word, by value**: a TCB's timer fields (offsets 3528..3576), or
a timer-tree or `REPROGRAM` word of a core's node. -/
theorem JAtZ.tw_word {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : P1.TW st Z.T Cs s b) :
    (∃ y ∈ Z.T, y.val + 3528 ≤ b.val ∧ b.val < y.val + 3576) ∨
    (∃ c ∈ Cs, ∃ o : Nat, (o = 104 ∨ o = 112) ∧ b.val = L.nodeBase s c + o) := by
  have hNP : ∀ c ∈ Cs, P1.NodePlaced st Z.T s c := fun c hc => by
    rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk c hc
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  rcases hb with ⟨y, hy, K, h1, h2, rfl⟩ | ⟨c', hc', o, ho, rfl⟩
  · left
    exact ⟨y, hy, by rw [Notif.tfield_val (hT y hy) (by omega)]; omega,
      by rw [Notif.tfield_val (hT y hy) (by omega)]; omega⟩
  · right; exact ⟨c', hc', o.val, ho, P1.nodeAt_val (hNP c' hc') (by omega)⟩

theorem JAtZ.tmw_word {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) :
    (∃ y ∈ Z.T, y.val + 3528 ≤ b.val ∧ b.val < y.val + 3576) ∨
    (∃ c ∈ Cs, ∃ o : Nat, (o = 104 ∨ o = 112 ∨ o = 56) ∧ b.val = L.nodeBase s c + o) := by
  rcases hb with hb | rfl
  · rcases J.tw_word hb with h | ⟨c, hc, o, ho, e⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, o, by omega, e⟩
  · right
    obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
    have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
    have hN : P1.NodePlaced st Z.T s Z.c := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
    have h56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    exact ⟨Z.c, hcC, 56, by omega, by rw [P1.nodeAt_val hN (by omega), h56]⟩

/-- **A timer word lies in no object of `H`** but a TCB's timer fields. -/
theorem JAtZ.tmw_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {p : U64} {k : P1.HKind} (hp : H p = some k)
    (hin : p.val ≤ b.val ∧ b.val < p.val + 2 ^ k.bits) :
    k = .tcb ∧ p ∈ Z.T ∧ p.val + 3528 ≤ b.val ∧ b.val < p.val + 3576 := by
  have hH := J.kern.heap
  rcases J.tmw_word hb with ⟨y, hy, g1, g2⟩ | ⟨c, hc, o, ho, e⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    by_cases hne : p = y
    · subst hne; rw [hHy] at hp; cases hp; exact ⟨rfl, hy, g1, g2⟩
    · have := hH.disj p _ y _ hp hHy hne
      have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
      rw [e12] at this; omega
  · have := J.kern.hnd p k hp c hc
    rcases ho with rfl | rfl | rfl <;> omega

/-- A timer word is no word of a non-TCB object of `H`. -/
theorem JAtZ.tmw_ne_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {p : U64} {k : P1.HKind} (hp : H p = some k) (hk : k ≠ .tcb)
    {w : U64} (hw : p.val ≤ w.val ∧ w.val < p.val + 2 ^ k.bits) : b ≠ w := fun e => by
  subst e; exact hk (J.tmw_obj hb hp hw).1

/-- A timer word is no TCB word off the timer fields. -/
theorem JAtZ.tmw_ne_tcb {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {t : U64} (ht : t ∈ Z.T) {w : U64} {K : Nat}
    (hwv : w.val = t.val + K) (hK : K < 3528 ∨ (3576 ≤ K ∧ K < 4096)) : b ≠ w := fun e => by
  subst e
  have := J.tmw_obj hb (J.zH.1 t ht) (by simp only [P1.HKind.bits]; omega)
  omega

/-- A timer word is no node word off the timer-tree and `REPROGRAM` words. -/
theorem JAtZ.tmw_ne_node {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {c : U64} (hc : c ∈ Cs) {o : U64} (ho : o.val < 4288)
    (h1 : o.val ≠ 104) (h2 : o.val ≠ 112) (h3 : o.val ≠ 56) : b ≠ L.nodeAt s c o := fun e => by
  have hN : P1.NodePlaced st Z.T s c := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk c hc
  have hv := P1.nodeAt_val hN ho
  have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
  rw [← e] at hv
  rcases J.tmw_word hb with ⟨y, hy, g1, g2⟩ | ⟨c', hc', o', ho', e'⟩
  · have := J.kern.hnd y _ (J.zH.1 y hy) c hc
    simp only [P1.HKind.bits] at this; omega
  · simp only [hnb] at hv e'
    by_cases hcc : c' = c
    · subst hcc; omega
    · have : c'.val ≠ c.val := fun h => hcc (UScalar.eq_of_val_eq h)
      rcases Nat.lt_or_gt_of_ne this with h | h
      · have : c'.val * 4288 + 4288 ≤ c.val * 4288 := by nlinarith
        omega
      · have : c.val * 4288 + 4288 ≤ c'.val * 4288 := by nlinarith
        omega

/-- `SlotsSame` across timer-word writes: the slots lie in `Z.th`'s objects,
which are `H`'s (`JPlaced`), at a TCB's cap slots (below offset 256). -/
theorem JAtZ.tmw_slots {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s)) : SlotsSame Z.th (L.mem s) (L.mem s') := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hPl := hJ.pl
  intro x hx
  have hf := hx.fit hPl
  have hal := hx.align hPl
  obtain ⟨p, i, hi, rfl⟩ := id hx
  have hv := hi.val hPl
  -- the slot's 32 bytes lie in `p`'s object of `H`, below 256 if a TCB
  have hin : ∃ k, H p = some k ∧ p.val + 32 * (i + 1) ≤ p.val + 2 ^ k.bits ∧ (k = .tcb → 32 * (i + 1) ≤ 256) := by
    rcases hi with ⟨r, hp, hr⟩ | ⟨hp, hr⟩
    · refine ⟨_, hJ.cnode p r hp, ?_, fun e => by cases e⟩
      simp only [P1.HKind.bits]
      have : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
      rw [this]
      have : i + 1 ≤ 2 ^ r := hr
      nlinarith
    · refine ⟨_, (hJ.tcb p).1 hp, ?_, fun _ => ?_⟩
      · simp only [P1.HKind.bits]; simp [tcbSlots] at hr; omega
      · simp [tcbSlots] at hr; omega
  obtain ⟨k, hHk, hsz, htcb⟩ := hin
  have w : ∀ kk : U64, kk.val < 32 → kk.val % 8 = 0 → L.mem s' (wordOf (slotOf p i) kk) = L.mem s (wordOf (slotOf p i) kk) := by
    intro kk hk hk8
    have hv' := wordOf_val (a := slotOf p i) (k := kk) (by omega)
    refine hw.2.2 _ (by unfold P1.Aligned; rw [hv']; omega) fun hb => ?_
    have g := J.tmw_obj hb hHk (by rw [hv', hv]; omega)
    have g2 := htcb g.1
    rw [hv', hv] at g
    omega
  refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
  have := w 0#u64 (by decide) (by decide)
  rwa [wordOf_zero] at this

set_option maxHeartbeats 2000000 in
/-- **The untyped caps' facts across timer-word writes** (`finW_utc`'s
argument: no timer word in an untyped cap's free part, the TCBs being typed
and the nodes outside every untyped region). -/
theorem JAtZ.tmw_utc {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (harch : σ'.archState = σ.archState)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
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
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [harch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases J.tmw_word hb with ⟨y, hy, g1, g2⟩ | ⟨c, hc, o, ho, e⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 c hc
      omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across timer-word writes** (module docstring): the timer words
written, `REPROGRAM` kept or set to 1, P1's `BlkOK` after given. -/
theorem JAtZ.tmw_step {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s))
    (hR : L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = L.mem s (L.nodeAt s Z.c layout.node.REPROGRAM) ∨
      L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = 1#u64)
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s') :
    ∃ r : Bool, JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a { σ with reprogramTimer := σ.reprogramTimer || r } := by
  obtain ⟨r, hX'⟩ := J.xtop.tmStep J.otherTmOK hw hR
  refine ⟨r, ?_⟩
  set σ' : Fl4Spec.State Unit := { σ with reprogramTimer := σ.reprogramTimer || r } with hσ'
  have F : Sched.NFr true σ.curThread σ σ' := Sched.NFr.rt _ σ _
  have hS := J.xtop.fin.1.1.1
  have hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hX'.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hks : L.ksb s' = L.ksb s := hw.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := J.kern.heap
  -- the frame words
  have k1 : ∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) := fun t ht =>
    hw.mem_eq (mcpA_aligned hT ht) fun hb => J.tmw_ne_tcb hb ht (mcpA_val hT ht) (by omega) rfl
  have k2 : ∀ t ∈ Z.T, L.mem s' (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    hw.mem_eq (yieldA_aligned hT ht) fun hb => J.tmw_ne_tcb hb ht (yieldA_val hT ht) (by omega) rfl
  have kb : ∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    hw.mem_eq (tIpcBufA_aligned (hT t ht)) fun hb => J.tmw_ne_tcb hb ht (tIpcBufA_val (hT t ht)) (by omega) rfl
  -- a word of an SC of `H`
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s' w = L.mem s w := fun q z hq w hal h1 h2 =>
    hw.mem_eq hal fun hb => J.tmw_ne_obj hb hq (fun e => by cases e) (by simp only [P1.HKind.bits]; omega) rfl
  have k3 : ∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj hS hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word hS hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s' (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧ L.mem s' (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      hw.mem_eq (J.rp.aligned hr ha) fun hb => J.tmw_ne_obj hb hHr (fun e => by cases e)
        (by simp only [P1.HKind.bits]; omega) rfl
    exact ⟨k _ (Or.inl (rPrevA_val hal)), k _ (Or.inr (rNextA_val hal))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal := hH.align q _ hq
    have hfit := hH.fits q _ hq
    have hz := hH.scmin q z hq
    simp only [P1.HKind.bits] at hal hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal]
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- the debug word and the IRQ node
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun hb => J.tmw_ne_node hb J.kern.cs0 (by simp)
      (by simp) (by simp) (by simp) rfl
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw J.kern.ksbFit J.kern.ksbAl fun b hb => by
      rcases J.tmw_word hb with ⟨y, hy, g1, g2⟩ | ⟨c, hc, o, ho, e⟩
      · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
      · simp only [P1.LawfulStore.nodeBase] at e; omega
  have hSS := J.tmw_slots hw
  -- the dead stay dead
  have hAI : ActIdle σ' := F.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep (G' := Z.G) hX' ⟨fun p => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun q hq => k3 q hq) hOut
      hAI.1 (J.yld.frame k2 F.ykeep) F.ykeep (J.jcov.dead q hq)
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hks hirq (J.idleW_keep hS' F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS' F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hSS hdead (J.idleW_keep hS' F.sk.idle F.sk.isc), hkern,
      J.tmw_utc hw hSS F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, J.inv.rt _,
      J.cur.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curInv, F.own J.own, F.off J.off,
      hAI, F.bsa J.bsa, F.isorted J.isorted,
      J.curRun.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curRunW, hblk⟩
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hw fun b hb =>
    J.notDbg_tw (fun y hy w K hwv h1 h2 => J.tmw_ne_tcb hb hy hwv (Or.inr ⟨h1, h2⟩))
      (fun c hc => J.tmw_ne_node hb hc (by simp [P1.debug_val]) (by simp [P1.debug_val]) (by simp [P1.debug_val])
        (by simp [P1.debug_val]))
  exact J.cs_frameK hks hX' F.kback F.ipcFr (JCs.same J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (fun t ht => hw.mem_eq (Sched.tVcpuA_aligned hT (J.thT t ht)) fun hb => J.tmw_ne_tcb hb (J.thT t ht) (Sched.tVcpuA_val hT (J.thT t ht)) (by omega) rfl)
    hSS hKd F.sk.idle


variable (arI) in
/-- **`send_signal` keeps `JAtZ`** [J] (module docstring): from `JAtZ` at a
notification of `N`, FL4's `send_signal` against the spec's `send_signal`
(deterministic, not failing), `JAtZ` after at fresh VSpace sets
(`XTopAt.irel_same`'s), the domain time kept. The IPC side is proved on
`IRel` (`send_signal_top`); the `JAtZ` lift (the footprint and spec frame
of a notification's wake: the dequeue or the bound receiver's
`cancel_ipc`, the restart, the SC donation, the switch, the sporadic
check) is not. -/
def SignalJHyp (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (n badge : U64), JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → n ∈ Z.N →
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄

/-- The loop's invariant: `JAtZ` at fresh VSpace sets after some fired
timers, the domain time kept. -/
def FireInv (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (σ : Fl4Spec.State Unit)
    (s : S) (a : A) : Prop :=
  ∃ (σ1 : Fl4Spec.State Unit) (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
    Fires σ σ1 ∧ σ1.domainTime = σ.domainTime ∧ JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s a σ1

set_option maxHeartbeats 8000000 in
/-- **The `REPROGRAM` write** at the end of a fired timer: `JAtZ` after,
`reprogram_timer` set. -/
theorem JAtZ.reprogramJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D
      (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64) a { σ with reprogramTimer := true } := by
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hN : P1.NodePlaced st Z.T s Z.c := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hal : P1.Aligned (L.nodeAt s Z.c layout.node.REPROGRAM) :=
    P1.nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  rw [hc.cur]
  have hw : P1.WritesIn st s (L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64) (TmW (L := L) Z.T Cs Z.c s) :=
    (P1.writesIn_wr hal).mono fun b hb => Or.inr hb
  have hblk := P1.reprogram.tinv (v := 1#u64) (P1.BlkOK.tinv J.blk)
  rw [hc.cur] at hblk
  obtain ⟨r, J'⟩ := J.tmw_step hw (Or.inr (P1.LawfulStore.mem_wr_same hal)) hblk
  have hrp := J'.xtop.fin.1.1.1.repr
  have e : (σ.reprogramTimer || r) = true := by
    have e1 : (σ.reprogramTimer || r) = decide (Sched.nodeW st (L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64)
      Z.c layout.node.REPROGRAM ≠ 0#u64) := hrp
    rw [e1]; unfold Sched.nodeW
    rw [P1.nodeAt_of_ksb (hw.1) Z.c layout.node.REPROGRAM, P1.LawfulStore.mem_wr_same hal]; simp
  rw [e] at J'
  exact J'

set_option maxHeartbeats 8000000 in
/-- **The TCB timers' loop keeps `FireInv`** (module docstring). -/
theorem fire_loopJ (hSig : SignalJHyp (L := L) arI AR H Cs) {σ : Fl4Spec.State Unit} (s : S) (a : A) (now i : U64)
    (h : FireInv (L := L) (arI := arI) AR Z H Cs σ s a) :
    timer.fire_loop st arI s a now i ⦃ r => FireInv (L := L) (arI := arI) AR Z H Cs σ r.1 r.2 ⦄ := by
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => FireInv (L := L) (arI := arI) AR Z H Cs σ x.1 x.2.1)
  · rintro ⟨s1, a1, i1⟩ h1
    try simp only at h1
    obtain ⟨σ1, V1, Ac1, Lst1, D1, hF1, hd1, J1⟩ := id h1
    have hTe : Z.T = P1.Heap.tcbs H := J1.tcbs_eq.1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with P1.LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with P1.obj.node_get.spec as ⟨t, et⟩
      step with P1.obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 h1
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := id J1.blk
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ P1.Heap.tcbs H := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with P1.obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 h1
      step with P1.obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (P1.timer.remove.tf (s0 := s1) s1 t (P1.TF.start (P1.BlkOK.tinv J1.blk)) htT) ?_
      rintro s2 ⟨h2, -, -, -, hw2⟩
      -- `timer::remove` keeps `JAtZ` and the spec state
      have hw2' : P1.WritesIn st s1 s2 (TmW (L := L) Z.T Cs Z.c s1) :=
        hw2.mono fun b hb => Or.inl (by rw [hTe]; exact hb)
      have hR2 : L.mem s2 (L.nodeAt s1 Z.c layout.node.REPROGRAM) = L.mem s1 (L.nodeAt s1 Z.c layout.node.REPROGRAM) := by
        obtain ⟨Q, R0, hc, -⟩ := J1.xtop.fin.1.1.1.lists
        have hcC : Z.c ∈ Cs := by have := J1.kern.cpuCs; rw [hc.cur] at this; exact this
        have hN : P1.NodePlaced st Z.T s1 Z.c := by rw [hTe]; exact P1.TInv.nodes J1.blk Z.c hcC
        refine hw2.mem_eq (P1.nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
          fun hb => ?_
        have hb' : P1.TW st Z.T Cs s1 (L.nodeAt s1 Z.c layout.node.REPROGRAM) := by rw [hTe]; exact hb
        have hv := P1.nodeAt_val hN (off := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM])
        have h56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
        rcases J1.tw_word hb' with ⟨y, hy, g1, g2⟩ | ⟨c', hc', o, ho, e⟩
        · have := J1.kern.hnd y _ (J1.zH.1 y hy) Z.c hcC
          simp only [P1.HKind.bits] at this; omega
        · have hnb : ∀ c, L.nodeBase s1 c = (L.ksb s1).val + 13568 + c.val * 4288 := fun _ => rfl
          simp only [hnb] at hv e
          by_cases hcc : c' = Z.c
          · subst hcc; omega
          · have : c'.val ≠ Z.c.val := fun h => hcc (UScalar.eq_of_val_eq h)
            rcases Nat.lt_or_gt_of_ne this with h | h
            · have : c'.val * 4288 + 4288 ≤ Z.c.val * 4288 := by nlinarith
              omega
            · have : Z.c.val * 4288 + 4288 ≤ c'.val * 4288 := by nlinarith
              omega
      obtain ⟨r2, J2⟩ := J1.tmw_step hw2' (Or.inl hR2) h2
      have e2 : (σ1.reprogramTimer || r2) = σ1.reprogramTimer := by
        have g1 : (σ1.reprogramTimer || r2) = decide (Sched.nodeW st s2 Z.c layout.node.REPROGRAM ≠ 0#u64) :=
          J2.xtop.fin.1.1.1.repr
        have g0 : σ1.reprogramTimer = decide (Sched.nodeW st s1 Z.c layout.node.REPROGRAM ≠ 0#u64) :=
          J1.xtop.fin.1.1.1.repr
        rw [g1, g0]; unfold Sched.nodeW
        rw [P1.nodeAt_of_ksb hw2.1, hR2]
      rw [e2] at J2
      have J2' : JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s2 a1 σ1 := J2
      step with P1.obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => ∃ (σ2 : Fl4Spec.State Unit) (V2 : XVs) (Ac2 : Set U64)
          (Lst2 : U64 → List U64) (D2 : Set U64), (σ2 = σ1 ∨ Signal σ1 σ2) ∧ σ2.domainTime = σ1.domainTime ∧
          JAtZ (L := L) arI AR (Z.mv Z.G V2) H Cs Ac2 Lst2 D2 r.1 r.2 σ2) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (P1.boundA t) ≠ 0#u64 := by rw [← en]; exact P1.bne_ne hn0
          have hnH : n ∈ P1.Heap.ntfns H := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hnN : n ∈ Z.N := J2'.hset.2.1 n hnH
          refine WP.spec_mono (hSig _ _ _ _ _ _ _ n bd J2' hnN) ?_
          rintro r ⟨σ2, V2, Ac2, Lst2, D2, hss, hd2, J3⟩
          exact ⟨σ2, V2, Ac2, Lst2, D2, Or.inr ⟨n.bv, bd.bv, hss⟩, hd2, J3⟩
        · exact (WP.spec_ok _).2 ⟨σ1, V1, Ac1, Lst1, D1, Or.inl rfl, rfl, J2'⟩
      rintro ⟨s3, a3⟩ ⟨σ2, V2, Ac2, Lst2, D2, hsig, hd2, J3⟩
      try simp only at J3
      try simp only [WP.uncurry'_pair]
      step with P1.LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with P1.obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      refine ⟨⟨{ σ2 with reprogramTimer := true }, V2, Ac2, Lst2, D2,
        Relation.ReflTransGen.tail hF1 ⟨σ2, hsig, rfl⟩, (hd2.trans hd1 : σ2.domainTime = σ.domainTime),
        J3.reprogramJ⟩, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

set_option maxHeartbeats 4000000 in
/-- **`JAtZ` across FL4's TCB timers** (module docstring). -/
theorem JAtZ.fireJ (hSig : SignalJHyp (L := L) arI AR H Cs) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    timer.fire st arI s a ⦃ r => FireInv (L := L) (arI := arI) AR Z H Cs σ r.1 r.2 ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (P1.obj.node_get.spec s c _) fun now _ => ?_
  exact fire_loopJ hSig s a now 0#u64 ⟨σ, Z.vs, Ac, Lst, D, Relation.ReflTransGen.refl, rfl, J⟩


set_option maxHeartbeats 4000000 in
/-- **The entry tail on `JAt` with the TCB timers proved** (`jat_scheduleT2`
with `hfireJ` discharged by `JAtZ.fireJ`, given `SignalJHyp` [J]): `JAtZ`
after FL4's `schedule` at fresh VSpace sets (the IPC side's `IRel` lift
fixes only the MDB ghost), the domain time nonzero before. -/
theorem jat_scheduleF {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hSig : SignalJHyp (L := L) arI AR H Cs)
    (hA : ArchSw st arI Z.N Z.T Z.C Z.c)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFoot st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ∧
        CurInv σ' ⦄ := by
  have h0Cs : 0#u64 ∈ Cs := J.kern.cs0
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hB := J.blk
  obtain ⟨⟨Q, R, hq⟩, hBd, hXi, hSc, hSg⟩ := id hB
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    P1.nodeAt_aligned (hq.nodes 0#u64 h0Cs) (by simp) (by simp)
  have hfire2 : timer.fire st arI s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1 ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1 ∧ NSC Z.N Z.C σ1 ∧ SchedPreW Z.T Z.C σ1 ∧
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 r.1 r.2 σ1) ∧
        timer.fire st arI s a = ok r ∧ L.ksb r.1 = L.ksb s) ⦄ := by
    refine WP.spec_mono (P1.spec_eq' (WP.spec_and (J.fireJ hSig) (P1.timer.fire.kw hAT hNt s a hB))) ?_
    rintro ⟨s1, a1⟩ ⟨hf, ⟨σ1, V1, Ac1, Lst1, D1, h1, hd1, J1⟩, hk⟩
    simp only [WP.uncurry'_pair] at hk
    have hd1' : σ1.domainTime ≠ 0 := by rw [hd1]; exact hd
    exact ⟨σ1, h1, J1.xtop.fin.1.1.1, J1.xtop.fin.1.1.2.2.1, J1.nsc, J1.schedPreW hd1',
      ⟨V1, Ac1, Lst1, D1, J1⟩, hf, hk.1⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and (schedule_refinesWP s a σ hS hR J.nsc hnd hfire2 hA hsni hsend hT)
    (P1.sched.schedule.kw hAT hNt s a hB)) (WP.spec_and (P1.sched.schedule.tinv hAT hNt s a Q R hq hBd hSc hXi hSg)
      hTail)) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA', rf, ⟨⟨V1, Ac1, Lst1, D1, J1⟩, hfr, hkf⟩, hw, hrun⟩,
    hkw⟩, ⟨htinv, hRest⟩⟩
  simp only [WP.uncurry'_pair] at hkw htinv
  obtain ⟨rf', hrf', -, hkw⟩ := hkw
  obtain rfl : rf = rf' := by simpa using (hrf'.symm.trans hfr).symm
  have hTl := hRest rf σ1 σ' D1 hF hsc hw hS' hI' hC' hA'
  obtain ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', -, -, -, -⟩ := htinv
  have hks' : L.ksb s' = L.ksb s := hkw.1.trans hkf
  have hnA : L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb hkf _ _
  have hdbg : L.mem s' (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) =
      L.mem rf.1 (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) := by
    exact hkw.mem_eq (by rw [hnA]; exact hal) (P1.dbg0_not_schedW J1.blk h0Cs)
  have hdw : (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val := by
    have hN0 := hq'.nodes 0#u64 h0Cs
    have hct : L.curW s' ∈ P1.Heap.tcbs H := hq'.curT
    have hv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp)
    have hsv := P1.field_val (hq'.tcbs _ hct) (K := 3328#u64) (by decide)
    have hdj := hN0.disj _ hct
    have hv' : (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s' 0#u64 + 88 := by
      rw [hnA, ← P1.nodeAt_of_ksb hks' 0#u64 layout.node.DEBUG_TCBS, hv, P1.debug_val]
    have hsv' : (P1.stA (L.curW s')).val = (L.curW s').val + 3328 := by
      rw [P1.stA_eq, hsv]; rfl
    rw [hv', hsv']
    have e12 : (2 : Nat) ^ 12 = 4096 := rfl
    rw [e12] at hdj
    omega
  obtain ⟨σ3, ho3, hr3, he3⟩ := hrun
  have hK1 : SchStep (fun _ => False) σ1 σ' := (schs_schedule.of_eq hsc).1
  have hL1 : LK (fun _ => False) σ1 σ' := lkm_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hSS : SlotsSame Z.th (L.mem rf.1) (L.mem s') :=
    slotsSame_of_iw J1.xtop.rel.1 J1.xtop.rel.2.2.2.2.2.1 J1.xtop.rel.2.2.2.2.2.2 hwT
      fun b hb => tfoot_iw J1.xtop.fin.1.1.1 hb
  obtain ⟨Qc, Rc, hcc, hsc'⟩ := hS'.lists
  obtain ⟨hth, hvt⟩ := hVt _ _ _ _ _ _ _ J1 _ hcc.curT
  have hcur : Vs.CurOK st Z.th s' σ' :=
    ⟨_, hsc'.curThread.symm, hth, fun p asid h => hvt p asid (by
      rwa [hSS.capAt ⟨_, 1, Or.inr ⟨hth, by decide⟩, rfl⟩] at h)⟩
  have hX' : XTopAt (L := L) AR (Z.mv Z.G V1) s' a' σ' :=
    xtop_sched_step J1.xtop J1.ip J1.nk hwT (ct := σ1.curThread)
      { hK1 with kh := fun p => (hK1.kh p).mono False.elim } hS' hR' hcur hTl.ar
  have hSOK1 := (schs_schedule.of_eq hsc).2
  have hY1 : YieldRel Z.T Z.C (L.mem s') σ' :=
    (ScAll.of_k J1.xtop.fin.1.1.1 J1.rp J1.yld J1.mcp J1.call J1.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hSOK1⟩).2.1
  have hdead : ∀ q ∈ D1, Sched.DeadP (L := L) H s' q := fun q hq =>
    J1.deadP_sch_step hX' hwT hK1 hL1 hA' (J1.ymd hS' hY1 ((hSOK1.ykeep rfl).dk q.bv)) (fun h => h)
      (J1.jcov.dead q hq)
  have hT2 : SchTailHyps (L := L) AR (Z.mv Z.G V1) H Cs D1 rf.1 s' a' σ' Ac :=
    ⟨hcur, hTl.ar, hdbg, hdw, hdead,
      ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', hSg.ksb' hks'⟩, P1.dbgKeep_schedW J1.blk J1.kern.ksbFit hkw⟩
  obtain ⟨Lst', J'⟩ := J1.sch_tail hsc hw hS' hR' hN' hI' hC' hA' (RunW.scAndTimer (hr3 J1.curRun) he3)
    (OffOK.scAndTimer ho3 he3) (bsa_schedule J1.bsa hsc) hT2
  exact ⟨σ', V1, Ac, Lst', D1, J', hC'⟩

end

end

end Fl4Proofs.P3
