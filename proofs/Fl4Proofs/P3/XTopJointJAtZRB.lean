/-
P3 (DESIGN.md §9), scheduler (KENTRY-PLAN.md sch9 (1)): **FL4's timers (`timer.fire`, `send_signal`) and `schedule` up to the scheduler action at `JAtZR`** (`JAtZR.fireJ`, `signalJHyp_ofZR`, `jat_scheduleWP0FZR`, `jat_scheduleFR2ZR`)

Scripted copies (sch9 gen.py: the transitive closure of the `JAtZ`-taking
lemmas used by the roots, with `JAtZ` -> `JAtZR`, `JRest` -> `JRestR`, other
copied names suffixed `ZR`); the proofs are the originals' except where
`cur` (now `CurInvR`, XTopJointJAtZR) is framed. Each section is headed by
its origin module.
-/
import Fl4Proofs.P3.XTopJointJAtZRA
import Fl4Proofs.P3.XTopJointJAtZRS
import Fl4Proofs.P3.ScNextDomCFR
import Fl4Proofs.P3.ScFireJ
import Fl4Proofs.P3.ScSignalBoundJ
import Fl4Proofs.P3.XTopJointCopyRegs
import Fl4Proofs.P3.XTopJointPP
import Fl4Proofs.P3.JEntryIrq
import Fl4Proofs.P3.ScSignalDonJ
import Fl4Proofs.P3.ScSignalJ
import Fl4Proofs.P3.XTopJointSchedRF
import Fl4Proofs.P3.XTopJointSchedRF2
import Fl4Proofs.P3.XTopJointSchedRF3
open Aeneas Aeneas.Std Result

-- ===== from ScFireJ
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

/-! LiveFrame's debug-word lemmas at `JAtZR` (KENTRY-PLAN g2j). -/

/-- **A word outside the TCBs and off the nodes' head words is no debug word.** -/
theorem JAtZR.notDbg' {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hobj : ∀ p, H p = some .tcb → b.val < p.val ∨ p.val + 2 ^ P1.HKind.bits .tcb ≤ b.val)
    (hnode : ∀ c ∈ Cs, b.val ≠ L.nodeBase s c + 88) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hT := hq.tcbs
  have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · have h1 := hobj y hy
    rw [e, show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, P1.field_val (hT y hy) (by simp), e12]
      at h1
    have : (3576#u64 : U64).val = 3576 := by simp
    omega
  · have h1 := hobj y hy
    rw [e, show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, P1.field_val (hT y hy) (by simp), e12]
      at h1
    have : (3584#u64 : U64).val = 3584 := by simp
    omega
  · have h1 := hnode c hc
    rw [e, P1.nodeAt_val (hq.nodes c hc) (by simp [P1.debug_val]), P1.debug_val] at h1
    exact h1 rfl

/-- **A word apart from the TCBs' debug links and the nodes' debug heads is no
debug word** (the links at TCB offsets 3576 and 3584). -/
theorem JAtZR.notDbg_tw {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (htcb : ∀ y ∈ Z.T, ∀ (w : U64) (K : Nat), w.val = y.val + K → 3576 ≤ K → K < 4096 → b ≠ w)
    (hnode : ∀ c ∈ Cs, b ≠ L.nodeAt s c layout.node.DEBUG_TCBS) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hT := hq.tcbs
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · have h3 : (3576#u64 : U64).val = 3576 := by simp
    exact htcb y (by rw [hTe]; exact hy) _ 3576
      (by rw [show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, P1.field_val (hT y hy) (by simp), h3])
      le_rfl (by norm_num) e
  · have h3 : (3584#u64 : U64).val = 3584 := by simp
    exact htcb y (by rw [hTe]; exact hy) _ 3584
      (by rw [show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, P1.field_val (hT y hy) (by simp), h3])
      (by norm_num) (by norm_num) e
  · exact hnode c hc e

/-- A kernel-state word (`KsW`) is no debug word: below the nodes, outside
the TCBs (`ksOut`). -/
theorem JAtZR.ksW_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : KsW (L.ksb s) b) : ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨K, h1, h2, -, e, -⟩ := hb
  refine J.notDbg' (fun p hp => ?_) (fun c _ => ?_)
  · obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
    have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
    rw [e12]
    rcases hq.ksOut p hp with h | h <;> omega
  · have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
    rw [hnb]; omega

/-- **A scheduler step's word is no debug word** (`SchW`: the TCBs' queue
words, the current node but its debug head, the domain words). -/
theorem JAtZR.schW_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : SchW (L := L) Z.T Z.c s b) : ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  have hS := J.xtop.fin.1.1.1
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
  rcases hb with ⟨y, hy, e | e | e⟩ | hn | hd
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · have hk : Sched.KFoot st Z.T Z.N Z.C Z.c s σ b := Sched.KFoot.of_sfoot (Or.inr ⟨hn.1, hn.2.1⟩)
    rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
    · exact Sched.KFoot.ne_tcbw hS hk (by rw [hTe]; exact hy) (K := 3576#u64) (by simp)
        (by unfold Sched.SOff Sched.SOffL; decide) e
    · exact Sched.KFoot.ne_tcbw hS hk (by rw [hTe]; exact hy) (K := 3584#u64) (by simp)
        (by unfold Sched.SOff Sched.SOffL; decide) e
    · obtain ⟨h1, h2, h3⟩ := hn
      have h4 := congrArg UScalar.val e
      rw [P1.nodeAt_val (hq.nodes c hc) (by simp [P1.debug_val]), P1.debug_val] at h4
      rw [hnb] at h1 h2 h3 h4
      omega
  · have hv := domKW_val hd
    refine J.notDbg' (fun p hp => ?_) (fun c _ => ?_)
    · have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
      rw [e12]; rcases hq.ksOut p hp with h | h <;> omega
    · rw [hnb]; omega

end

section Spec
open Fl4Spec
end Spec
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A `CnW` word is no TCB's VCPU word** (`JAtZ.cnW_nv` at `JAtZR`;
KENTRY-PLAN g2b). -/
theorem JAtZR.cnW_nv {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b) : ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  have hS := J.xtop.fin.1.1.1
  have hH := J.kern.heap
  intro t ht
  have hv := Sched.tVcpuA_val J.ip.e.tcb ht
  have hHt : H t = some .tcb := J.zH.1 t ht
  rcases hb with hb | ⟨e, he, h⟩ | ⟨r, hr, h⟩
  · exact FinW.nv hS hb t ht
  · rintro rfl
    have hHe : H e = some .ep := J.zH.2.1 e he
    have hne : e ≠ t := fun h' => by rw [h', hHt] at hHe; cases hHe
    have := hH.disj e _ t _ hHe hHt hne
    unfold EW at h; simp only [P1.HKind.bits] at this; omega
  · rintro rfl
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have hne : r ≠ t := fun h' => by rw [h', hHt] at hHr; cases hHr
    have := hH.disj r _ t _ hHr hHt hne
    simp only [P1.HKind.bits] at this; omega

/-- **A timer word, by value**: a TCB's timer fields (offsets 3528..3576), or
a timer-tree or `REPROGRAM` word of a core's node. -/
theorem JAtZR.tw_word {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
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


theorem JAtZR.tmw_word {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
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
theorem JAtZR.tmw_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
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
theorem JAtZR.tmw_ne_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {p : U64} {k : P1.HKind} (hp : H p = some k) (hk : k ≠ .tcb)
    {w : U64} (hw : p.val ≤ w.val ∧ w.val < p.val + 2 ^ k.bits) : b ≠ w := fun e => by
  subst e; exact hk (J.tmw_obj hb hp hw).1


/-- A timer word is no TCB word off the timer fields. -/
theorem JAtZR.tmw_ne_tcb {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {t : U64} (ht : t ∈ Z.T) {w : U64} {K : Nat}
    (hwv : w.val = t.val + K) (hK : K < 3528 ∨ (3576 ≤ K ∧ K < 4096)) : b ≠ w := fun e => by
  subst e
  have := J.tmw_obj hb (J.zH.1 t ht) (by simp only [P1.HKind.bits]; omega)
  omega


/-- A timer word is no node word off the timer-tree and `REPROGRAM` words. -/
theorem JAtZR.tmw_ne_node {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
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
theorem JAtZR.tmw_slots {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
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
theorem JAtZR.tmw_utc {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
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
/-- **`JAtZR` across timer-word writes** (module docstring): the timer words
written, `REPROGRAM` kept or set to 1, P1's `BlkOK` after given. -/
theorem JAtZR.tmw_step {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s))
    (hR : L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = L.mem s (L.nodeAt s Z.c layout.node.REPROGRAM) ∨
      L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = 1#u64)
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s') :
    ∃ r : Bool, JAtZR (L := L) arI AR Z H Cs Ac Lst D s' a { σ with reprogramTimer := σ.reprogramTimer || r } := by
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
  have R : JRestR (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hSS hdead (J.idleW_keep hS' F.sk.idle F.sk.isc), hkern,
      J.tmw_utc hw hSS F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, J.inv.rt _,
      fun e => F.curInv (J.cur (by rw [← (F.act rfl).1]; exact e)), F.own J.own, F.off J.off,
      hAI, F.bsa J.bsa, F.isorted J.isorted,
      J.curRun.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curRunW, hblk⟩
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hw fun b hb =>
    J.notDbg_tw (fun y hy w K hwv h1 h2 => J.tmw_ne_tcb hb hy hwv (Or.inr ⟨h1, h2⟩))
      (fun c hc => J.tmw_ne_node hb hc (by simp [P1.debug_val]) (by simp [P1.debug_val]) (by simp [P1.debug_val])
        (by simp [P1.debug_val]))
  exact J.cs_frame (G' := Z.G) hks hX' F.kback F.ipcFr (JCs.sameZR J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (fun t ht => hw.mem_eq (Sched.tVcpuA_aligned hT (J.thT t ht)) fun hb => J.tmw_ne_tcb hb (J.thT t ht) (Sched.tVcpuA_val hT (J.thT t ht)) (by omega) rfl)
    (J.liveX hX' rfl rfl rfl hSS hKd F.sk.orig (J.idleW_keep hS' F.sk.idle F.sk.isc).1
      fun p hp => R.jcov.dead p (J.zD p hp)) (J.zDX hSS J.zD)



variable (arI) in
/-- **`send_signal` keeps `JAtZR`** [J] (module docstring): from `JAtZR` at a
notification of `N`, FL4's `send_signal` against the spec's `send_signal`
(deterministic, not failing), `JAtZR` after at fresh VSpace sets
(`XTopAt.irel_same`'s), the domain time kept. The IPC side is proved on
`IRel` (`send_signal_top`); the `JAtZR` lift (the footprint and spec frame
of a notification's wake: the dequeue or the bound receiver's
`cancel_ipc`, the restart, the SC donation, the switch, the sporadic
check) is not. -/
def SignalJHypZR (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (n badge : U64), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → n ∈ Z.N →
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄

variable (arI) in
/-- **`SignalJHypZR` at the states satisfying `P`** (g3b): the signal step only
where the caller has `P` (`P := NativeScope`, carried by the spec along the
fired timers, for `kernel_entryJ28`; `P := True` is `SignalJHypZR`). -/
def SignalJHypZRP (P : Fl4Spec.State Unit → Prop) (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) :
    Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (n badge : U64), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → P σ → n ∈ Z.N →
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄


/-- The loop's invariant: `JAtZR` at fresh VSpace sets after some fired
timers, the domain time kept. -/
def FireInvZR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (σ : Fl4Spec.State Unit)
    (s : S) (a : A) : Prop :=
  ∃ (σ1 : Fl4Spec.State Unit) (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
    Fires σ σ1 ∧ σ1.domainTime = σ.domainTime ∧ JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s a σ1


set_option maxHeartbeats 8000000 in
/-- **The `REPROGRAM` write** at the end of a fired timer: `JAtZR` after,
`reprogram_timer` set. -/
theorem JAtZR.reprogramJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    JAtZR (L := L) arI AR Z H Cs Ac Lst D
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
/-- **The TCB timers' loop keeps `FireInvZR`** (module docstring). -/
theorem fire_loopJZR (P : Fl4Spec.State Unit → Prop) {σ : Fl4Spec.State Unit} (hP : ∀ σ1, Fires σ σ1 → P σ1)
    (hSig : SignalJHypZRP (L := L) arI P AR H Cs) (s : S) (a : A) (now i : U64)
    (h : FireInvZR (L := L) (arI := arI) AR Z H Cs σ s a) :
    timer.fire_loop st arI s a now i ⦃ r => FireInvZR (L := L) (arI := arI) AR Z H Cs σ r.1 r.2 ⦄ := by
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => FireInvZR (L := L) (arI := arI) AR Z H Cs σ x.1 x.2.1)
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
      -- `timer::remove` keeps `JAtZR` and the spec state
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
      have J2' : JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s2 a1 σ1 := J2
      step with P1.obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => ∃ (σ2 : Fl4Spec.State Unit) (V2 : XVs) (Ac2 : Set U64)
          (Lst2 : U64 → List U64) (D2 : Set U64), (σ2 = σ1 ∨ Signal σ1 σ2) ∧ σ2.domainTime = σ1.domainTime ∧
          JAtZR (L := L) arI AR (Z.mv Z.G V2) H Cs Ac2 Lst2 D2 r.1 r.2 σ2) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (P1.boundA t) ≠ 0#u64 := by rw [← en]; exact P1.bne_ne hn0
          have hnH : n ∈ P1.Heap.ntfns H := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hnN : n ∈ Z.N := J2'.hset.2.1 n hnH
          refine WP.spec_mono (hSig _ _ _ _ _ _ _ n bd J2' (hP σ1 hF1) hnN) ?_
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
/-- **`JAtZR` across FL4's TCB timers** (module docstring). -/
theorem JAtZR.fireJ (P : Fl4Spec.State Unit → Prop) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hP : ∀ σ1, Fires σ σ1 → P σ1) (hSig : SignalJHypZRP (L := L) arI P AR H Cs)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    timer.fire st arI s a ⦃ r => FireInvZR (L := L) (arI := arI) AR Z H Cs σ r.1 r.2 ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (P1.obj.node_get.spec s c _) fun now _ => ?_
  exact fire_loopJZR P hP hSig s a now 0#u64 ⟨σ, Z.vs, Ac, Lst, D, Relation.ReflTransGen.refl, rfl, J⟩



end
end
end Fl4Proofs.P3
-- ===== from ScSignalBoundJ
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
theorem JAtZR.donCore {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) :
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


/-- **A `CnX` word is in no other object of `H`** (module docstring): not in
an object `p` of `H` other than an endpoint or reply, nor in a reply's words
other than its `TCB` word. -/
theorem JAtZR.cnX_not (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : CnX Z.E Z.R b)
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


/-- **The frame words a `CnW` step keeps** (`finW_keeps`). -/
theorem JAtZR.cnW_keeps (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
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
theorem JAtZR.cnW_scOut (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
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
theorem JAtZR.cnW_irq (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
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
theorem JAtZR.cnW_utc (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
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
theorem JAtZR.deadP_cfr (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {r t : Fl4Spec.ObjRef} {s3 : S}
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


variable (arI) in
/-- **A reply naming a thread blocked receiving is detached and unlinked**
(module docstring): on no call stack and with null `prev`/`next` words, at
every `JAtZR` (`recvReplyHyp_holdsZR`, from `JAtZR.rrecv`). -/
def RecvReplyHypZR (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit),
    JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → ∀ d ∈ Z.R, ∀ xr t xt, σ.kheap d.bv = some (.reply xr) →
      xr.replyTcb = some t → σ.kheap t = some (.tcb xt) → Fl4Spec.receiveBlocked xt.tcbState = true →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64


/-- **`RecvReplyHypZR` holds** (formerly the [J] premise `RecvReplyLinksHyp`):
`JAtZR.rrecv` (ScRecvLinks) gives the null links, `detached_of_next0` the
rest. -/
theorem recvReplyHyp_holdsZR : RecvReplyHypZR (L := L) arI AR H Cs := by
  intro Z Ac Lst D s a σ J d hd xr t xt hx ht hxt hrb
  obtain ⟨hn, hp⟩ := J.rrecv d hd ⟨xr, t, xt, hx, ht, hxt, hrb⟩
  exact ⟨detached_of_next0 J.call (fun r hr => (J.rp.align r hr).2.1) hn, hn, hp⟩


set_option maxHeartbeats 8000000 in
/-- **The bound-receiver wake keeps `JAtZR`** (module docstring). -/
theorem JAtZR.wake_postB (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {n t : Fl4Spec.ObjRef}
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : CFr n t σ σ') (I3 : Inv σ') (B3 : BlockedScActive σ') (hAI3 : ActIdle σ')
    (hcur3 : CurInvR σ') (hrun3 : CurRunM σ')
    (hRR : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb = some t →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∃ V' : XVs, JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
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
  have R : JRestR (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.cnW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, B3, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.sameZR J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩


set_option maxHeartbeats 8000000 in
/-- **`send_signal` to an idle notification bound to a thread blocked
receiving, without SC donation, keeps `JAtZR`** (module docstring): FL4's side
`send_signal_bound_irel`, the spec's `cancelIpc_recv_cfr`, `cancel_recv_inv`,
`wake_specB`, then `wake_postB`. -/
theorem JAtZR.signal_boundJ (hAT : P0.ArchTotal arI) (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn) {t : U64} {tcb : Fl4Spec.Tcb}
    (hb : x.ntfnBoundTcb = some t.bv) (hkt : σ.kheap t.bv = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) (hND : NoDon Z.C σ t.bv n.bv) (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
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
  have hcur1 : CurInvR σ1 := fun e => F1.curInv (J.cur
    (hact1.elim (fun e1 => by rw [← e1]; exact e) (fun e1 => by rw [e1] at e; cases e)))
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
  obtain ⟨I', B', F2, AI', cur', run'⟩ := wake_specBR hI1 hB1 hAI1 hcur1 hrun1 hk1 hin hrib hsa hdon hmw
  have hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    (hW1.trans (hFS.1.mono fun b hb => FinW.back hW1.1 (SzKeepC.of F1.szKeep) hb)).mono
      fun b h => h.elim id Or.inl
  have hRR : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb = some t.bv →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64 :=
    fun d hd xr hx' hxt => recvReplyHyp_holdsZR Z Ac Lst D s _ σ J d hd xr t.bv tcb hx' hxt hkt hrb
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
-- ===== from XTopJointCopyRegs
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
  {s : S} {ar : A} {σ : Fl4Spec.State Unit}
set_option maxHeartbeats 4000000 in
/-- **A scheduler step at `J`** (`stepClosed_jat`'s scheduler case, with
XTopJointRest's `jowes_schedZR`, no premise). -/
theorem JAtZR.schedJ (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s ar σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS : SchedStep (L := L) Z.th s σ s' σ') :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZR (L := L) arI AR Z H Cs Ac' Lst' D' s' ar σ' := by
  have hX := J.xtop
  have hX1 := hX.schedStep J.ks J.thT hS
  have hW := (hS.2.1 Z.N Z.T Z.C Z.c J.thT hX.fin.1.1.1 hX.fin.1.1.2.2.1).2.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    hX.slotsSame_of hW fun b hb => schW_oobj hX.fin.1.1.1.placed.tcb hb
  obtain ⟨Ac', Lst', R⟩ := jowes_schedZR arI s s' ar σ σ' hS Z H Cs Ac Lst D rfl J hX1
  exact ⟨Ac', Lst', D, J.cs_frame hW.1 hX1 (KBack.of_kheap hS.1.kh) (IpcFrKeep.of_kheap hS.1.kh) (JCs.sameZR J hSS (KSz.of_kheap hS.1.kh)) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (VKeep.of_writes J.ip.e.tcb J.thT hW fun _ hb => J.schW_nv hb)
    (J.liveX hX1 rfl rfl rfl hSS (dbgKeep_of_writes J.blk hW fun _ hb => J.schW_notDbg hb)
      (orig_eq_of_slots J.xtop.rel.2.1.2.2.2.1 hX1.rel.2.1.2.2.2.1 J.kern.orig R.kern.orig hSS)
      (XTopAt.idleW_eqS hX hX1 hS.1.idle) fun p hp => R.jcov.dead p (J.zD p hp))
    (J.zDX hSS J.zD)⟩


end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
end
end
end Fl4Proofs.P3
-- ===== from XTopJointPP
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
set_option maxHeartbeats 4000000 in
/-- **A write of `WORK_UNITS` keeps `JAtZR`** (module docstring). -/
theorem JAtZR.workUnitsJD {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (v : U64) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64),
      JAtZR (L := L) arI AR Z H Cs Ac' Lst' D
        (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) v) a σ := by
  have hX := J.xtop
  have hf := J.kern.ksbFit
  have hal := J.kern.ksbAl
  have hv := workUnits_val hf
  set w := core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS with hwd
  have ha : P1.Aligned w := by unfold P1.Aligned; rw [hv]; omega
  set s' := L.wr s w v with hs'
  have hw : P1.WritesIn st s s' (KsW (L.ksb s)) :=
    (P1.writesIn_wr ha).mono fun b hb => ⟨40#u64, by decide, by decide, by decide, by rw [hb, hv]; rfl,
      Or.inl (by decide)⟩
  have hne : ∀ b : U64, P1.Aligned b → b.val ≠ (L.ksb s).val + 40 → L.mem s' b = L.mem s b := fun b hb hb' =>
    P1.LawfulStore.mem_wr_ne ha hb (by rw [hv]; omega)
  have hirq : IrqRel (L.mem s') (L.ksb s) σ := by
    have hR := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, hR.node⟩
    have e := irqStA_val hf hi
    rw [hne _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega)]
    exact hR.st i hi
  have hio : IoRel (L.mem s') (L.ksb s) σ := by
    have hR := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hw' : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have e := ioA_val hf hw'
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega)]
    exact hR p hp
  have hdk : DK4 (L := L) s s' := ⟨by rw [hs', P1.LawfulStore.ksb_wr], fun o ho => by
    obtain ⟨h1, h2⟩ := domOffs0_lt ho
    have e : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have h40 : o.val ≠ 40 := by
      simp only [domOffs0, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    exact hne _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega)⟩
  have hD := hX.rel.2.2.2.1
  have hAR := hX.fin.1.1.2.2.2.2.2.2
  have hX1 : XTopAt (L := L) AR Z s' a σ := XTopAt.ksStep hX J.ks hw (KsStep.refl σ) hirq hio
    (hD.frame (fun o ho => hdk.2 o ho) rfl rfl) hAR
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    hX.slotsSame_of hw fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨Ac', Lst', R⟩ := jowes_ksDZR arI s s' a a σ σ hw (KsStep.refl σ) Z H Cs Ac Lst D rfl J hX1
  exact ⟨Ac', Lst', J.cs_frame hw.1 hX1 (KBack.of_kheap rfl) (IpcFrKeep.of_kheap rfl) (JCs.sameZR J hSS (KSz.of_kheap rfl)) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (VKeep.of_writes J.ip.e.tcb J.thT hw fun _ hb => J.ksW_nv hb)
    (J.liveX hX1 rfl rfl rfl hSS (dbgKeep_of_writes J.blk hw fun _ hb => J.ksW_notDbg hb) rfl
      (XTopAt.idleW_eqS hX hX1 rfl) fun p hp => R.jcov.dead p (J.zD p hp))
    (J.zDX hSS J.zD)⟩


end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
end
end
end Fl4Proofs.P3
-- ===== from JEntryIrq
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
noncomputable section
section Named
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
end Named
section J
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
namespace JAtZR
/-- **P1's kernel-write words of `JAtZR`'s sets miss the domain schedule**
(IrqDom's `KWApart`), at any state with the same kernel-state base whose
cores' nodes are placed (P1's `TimerOK.npl`). -/
theorem kwApartJ (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hk : L.ksb s' = L.ksb s)
    (hN : ∀ c ∈ Cs, P1.NodePlaced st (P1.Heap.tcbs H) s' c) :
    KWApart (L := L) (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s' := by
  have hf := J.kern.ksbFit
  have hal := J.kern.ksbAl
  have hks := J.kern.hks
  have hH := J.kern.heap
  intro b hb hkw
  unfold P1.Aligned at hb
  suffices h : b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val by rw [hk]; exact h
  -- a word of an `H` object that is not an `other` one
  have hobj : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → p.val ≤ b.val → b.val < p.val + 2 ^ k.bits →
      b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val := by
    intro p k hp hk' h1 h2
    have h3 := hks p k hp hk'
    generalize 2 ^ k.bits = N at h2 h3
    omega
  rcases hkw with ⟨y, hy, K, hK1, hK2, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hsg | ⟨c, hc, hin⟩ |
      ⟨e, he, rfl | rfl⟩
  · -- a TCB word
    have hy' : H y = some .tcb := hy
    have hfit := hH.fits y _ hy'
    simp only [P1.HKind.bits] at hfit
    have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
    rw [h12] at hfit
    have hv : (core.num.U64.wrapping_add y K).val = y.val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine hobj y .tcb hy' (fun z h => by cases h) (by rw [hv]; omega) ?_
    rw [hv]; simp only [P1.HKind.bits, h12]; omega
  · -- a node word
    have hv := P1.nodeAt_val (hN c hc) ho
    unfold P1.LawfulStore.nodeBase at hv
    rw [hk] at hv
    rw [hv]; omega
  · -- a reply's, SC's or notification's frame word
    obtain ⟨-, p, k, hp, hk', hin⟩ := hsg
    have hko : ∀ z, k ≠ .other z := by
      rcases hk' with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> exact fun z h => by cases h
    exact hobj p k hp hko hin.1 hin.2
  · -- an SC word
    obtain ⟨z, hz⟩ := hc
    have hzb : P1.Heap.scBits H c = z := by simp [P1.Heap.scBits, hz]
    rw [hzb] at hin
    exact hobj c (.sc z) hz (fun _ h => by cases h) hin.1 (by simpa [P1.HKind.bits] using hin.2)
  all_goals
    obtain ⟨k, hek, hk4, hko⟩ : ∃ k, H e = some k ∧ 4 ≤ k.bits ∧ ∀ z, k ≠ .other z := by
      rcases he with h | h
      · exact ⟨_, h, by simp [P1.HKind.bits], fun z h => by cases h⟩
      · exact ⟨_, h, by simp [P1.HKind.bits], fun z h => by cases h⟩
    have hfit := hH.fits e k hek
    have h16 : (16 : Nat) ≤ 2 ^ k.bits :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk4)
  · -- an endpoint's or notification's head word
    exact hobj e k hek hko (by rw [P1.epHeadA_val]) (by rw [P1.epHeadA_val]; omega)
  · -- its tail-state word
    have hv := P1.epTSA_val' (e := e) (by omega)
    rcases hks e k hek hko with h | h
    · left; rw [hv]
      generalize 2 ^ k.bits = N at h h16
      omega
    · right; rw [hv]; omega


end JAtZR
end J
end
end Fl4Proofs.P3
-- ===== from ScSignalDonJ
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
/-- A notification's SC is not dead (bound back to the notification,
`JAtZR.ntfn_link`; a dead SC's notification word is `0`). -/
theorem JAtZR.ntfnSc_not_dead (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64} {y : Fl4Spec.SchedContext}
    {k : Nat} (hq : σ.kheap q.bv = some (.schedContext y k)) {o : Fl4Spec.ObjRef} {xo : Fl4Spec.Notification}
    (ho : σ.kheap o = some (.notification xo)) (hsc : xo.ntfnSc = some q.bv) : ¬ DeadP (L := L) H s q := by
  intro hd
  obtain ⟨n', hn', en⟩ := J.obj.ntfn o xo ho
  subst en
  obtain ⟨y', m', hky, hyn⟩ := J.ntfn_link hn' xo q.bv ho hsc
  rw [hq] at hky; cases hky
  obtain ⟨c', hc', ec⟩ := J.obj.sc q.bv y k hq
  have hcq : c' = q := P1.eq_of_bv ec
  subst hcq
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨-, hH⟩ := hJ.sc c' y k (J.c0 c' hc') hq
  obtain ⟨-, -, d3, -⟩ := hd.2.2.2.2 _ hH
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x, m, hkx, hR⟩ := hs.scs c' hc'
  rw [hq] at hkx; cases hkx
  have h1 := hR.ntfn
  rw [scW_ntfn] at h1
  rw [show L.mem s (scNtfnA c') = 0#u64 from d3, optRef_zero, hyn] at h1
  cases h1


set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a `DWFr` step** with the footprint `CnW`
(`deadP_cfr`; `t` was blocked, so not dead; an SC whose thread changes is a
notification's SC, so not dead). -/
theorem JAtZR.deadP_dfr (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {r t : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : DWFr r t σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
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
  · -- a dead TCB: its state, (null) bound notification and SC kept
    obtain ⟨t', ht', e⟩ := J.obj.tcb q.bv x hx
    have htq : t' = q := P1.eq_of_bv e
    subst htq
    obtain ⟨-, -, d3, -, -⟩ := hd.1 (J.zH.1 t' ht')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t' ht'
    rw [hx] at hk'; cases hk'
    have hbn : x.tcbBoundNotification = none := by
      rw [hR.bound, show tBoundA t' = P1.boundA t' from rfl, d3, optRef_zero]
    obtain ⟨st', bn, fl, ar, sc, hk3, hs⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, ?_, ?_⟩
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
    · show sc = x.tcbSchedContext ∨ sc = none
      by_cases e : sc = x.tcbSchedContext
      · exact Or.inl e
      · exact absurd (F.tsc _ x _ hx hk3 e).1 (ht t' hq)
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
  · -- an SC: its thread kept (a changed one is a notification's SC, not dead), its notification kept or cut
    obtain ⟨rf, nt, tc, hk3, -, hn⟩ := F.scF hx
    refine ⟨_, hk3, ?_, hn⟩
    show tc = x.scTcb ∨ tc = none
    by_cases e : tc = x.scTcb
    · exact Or.inl e
    · obtain ⟨-, o, xo, ho, hsc⟩ := F.scb q.bv x n _ n hx hk3 e
      exact absurd hd (J.ntfnSc_not_dead hx ho hsc)


set_option maxHeartbeats 8000000 in
/-- **A wake with or without a donation keeps `JAtZR`** (`wake_postB` in the
frame `DWFr`). -/
theorem JAtZR.wake_postD (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {n t : Fl4Spec.ObjRef}
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : DWFr n t σ σ') (I3 : Inv σ') (B3 : BlockedScActive σ') (hAI3 : ActIdle σ')
    (hcur3 : CurInvR σ') (hrun3 : CurRunM σ')
    (hRR : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb = some t →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64)
    (ht : ∀ q ∈ D, q.bv ≠ t) (htT : ∃ u ∈ Z.T, u.bv = t) :
    ∃ V' : XVs, JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
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
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_dfr F hS3 hIR.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep ht
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
  have R : JRestR (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.cnW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own htT J.own, F.off J.off,
      hAI3, B3, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.sameZR J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩


/-- A thread in a state other than `inactive` is not dead. -/
theorem JAtZR.not_dead_of_st (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (htT : t ∈ Z.T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hst : tsCode xt.tcbState ≠ 0) :
    ∀ q ∈ D, q.bv ≠ t.bv := by
  intro q hq eq
  have hqt : q = t := P1.eq_of_bv eq
  subst hqt
  have d1 := ((J.jcov.dead q hq).1 (J.zH.1 q htT)).1
  have hI := J.xtop.irelK J.ks J.buf
  have h3 := (hI.1.toN.at_tcb htT hkt).st
  rw [P1.stA_eq, ← tStA_eq] at d1
  rw [d1] at h3
  unfold sched.TS_INACTIVE at h3
  exact hst (by rw [← h3]; rfl)


set_option maxHeartbeats 8000000 in
/-- **A waiting notification signalled, donating or not, keeps `JAtZR`**
(module docstring). -/
theorem JAtZR.signal_waitDJ (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {l : List Fl4Spec.ObjRef} (ho : x.ntfnObj = .waitingNtfn l)
    (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hNt : ∀ m ∈ P1.Heap.ntfns H, H m = some .ntfn := fun _ h => h
  have hnH : n ∈ P1.Heap.ntfns H := J.zH.2.2.2 n hn
  have hbl := (J.sv.ntfnQ n.bv x hk).2
  refine WP.spec_mono (WP.spec_and (send_signal_wait_irelD J.ip hmb s a σ hI J.inv J.nsc hn hk ho hbl badge)
    (P1.notification.send_signal.tinvF hAT s a n badge J.blk hnH (hNt n hnH))) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, d, xd, σd, σ', hmq, hkd, hxs, hdon, hsend, hmw, hIR, hF, hFS⟩, hb⟩
  try simp only [WP.uncurry'_pair] at hb
  obtain ⟨hb, -, hfoot⟩ := hb
  have hfoot := hfoot (J.donCore hn)
  subst ea
  have hdn : d.bv ≠ n.bv := by intro e; rw [e, hk] at hkd; cases hkd
  set σ1 := updK σ n.bv (.notification (afterDequeue x d)) with hσ1
  have hk1 : σ1.kheap d.bv = some (.tcb xd) := by simp [hσ1, updK, hdn, hkd]
  have hkn1 : σ1.kheap n.bv = some (.notification (afterDequeue x d)) := by simp [hσ1, updK]
  have hkp1 : ∀ p, p ≠ n.bv → σ1.kheap p = σ.kheap p := fun p hp => by simp [hσ1, updK, hp]
  have hsub : (afterDequeue x d).ntfnObj.ntfnQueue.Sublist x.ntfnObj.ntfnQueue := by
    show (match Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x) with
      | [] => Fl4Spec.Ntfn.idleNtfn
      | _ => Fl4Spec.Ntfn.waitingNtfn (Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x))).ntfnQueue.Sublist
        (Fl4Spec.ntfnQueueOf x)
    split
    · exact List.nil_sublist _
    · unfold Fl4Spec.removeAll; apply List.filter_sublist
  have F1 : NFr false n.bv σ σ1 :=
    NFr.upd hk (Or.inr (Or.inr ⟨x, afterDequeue x d, rfl, rfl, rfl, hsub, (fun h => by cases h), Or.inl rfl,
      fun hw => absurd ho (hw l), Or.inl rfl⟩))
  have hI1 : Inv σ1 := J.inv.updNtfn hk (fun p hp => J.inv.ntfnSc n.bv x p hk hp)
  have hAI1 : ActIdle σ1 := ⟨fun u hu => F1.sched (J.act.1 u hu), F1.idleOK J.act.2⟩
  have hcur1 : CurInvR σ1 := fun e => F1.curInv (J.cur e)
  have hrun1 : CurRunM σ1 := Or.imp id F1.curRunW J.curRun
  have hoff1 : OffOK σ1 := F1.off J.off
  have hsp1 : ∀ c y k, σ1.kheap c = some (.schedContext y k) → y.scSporadic = true → Fl4Spec.scActive y = true := by
    intro c y k hc
    have hcn : c ≠ n.bv := by rintro rfl; rw [hkn1] at hc; cases hc
    rw [hkp1 c hcn] at hc
    exact J.sv.scSpor c y k hc
  obtain ⟨I', B', F2, AI', cur', run'⟩ := wake_specGR hI1 (wake_inv3 hI1 hk1 hxs badge.bv) (F1.bsa J.bsa) hAI1
    hcur1 hrun1 hk1 (by rw [hxs]; rfl) (CFr.ofNFr (wake_f3 hk1 hxs badge.bv)) hkn1 hoff1 hsp1 hdon hmw
  have FF : DWFr n.bv d.bv σ σ' := (DWFr.ofNFr F1).trans F2
  have hdT : d ∈ Z.T := by
    obtain ⟨t', ht', e⟩ := J.obj.tcb d.bv xd hkd
    rw [← P1.eq_of_bv e]; exact ht'
  have hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hFS.1.mono fun b h => Or.inl h
  have hRR : ∀ q ∈ Z.R, ∀ xr, σ.kheap q.bv = some (.reply xr) → xr.replyTcb = some d.bv →
      Detached Z.C Lst q ∧ L.mem s (rNextA q) = 0#u64 ∧ L.mem s (rPrevA q) = 0#u64 := by
    intro q _ xr hq hxt
    exfalso
    obtain ⟨x', hk', hs'⟩ := J.sv.replyTcb q.bv xr d.bv hq hxt
    rw [hkd] at hk'; cases hk'
    rcases hs' with e | ⟨ep, dd, e⟩ <;> rw [hxs] at e <;> cases e
  have htD := J.not_dead_of_st hdT hkd (by rw [hxs]; simp [tsCode])
  obtain ⟨V', J'⟩ := J.wake_postD hIR hF hw hb hfoot FF I' B' AI' cur' run' hRR htD ⟨d, hdT, rfl⟩
  exact ⟨σ', V', Ac, Lst, D, hsend, FF.sk.dt, J'⟩


set_option maxHeartbeats 8000000 in
/-- **The idle notification's bound receiver woken, donating or not, keeps
`JAtZR`** (module docstring; `JAtZR.signal_boundJ` with `wake_specG`). -/
theorem JAtZR.signal_boundDJ (hAT : P0.ArchTotal arI) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn) {t : U64} {tcb : Fl4Spec.Tcb}
    (hb : x.ntfnBoundTcb = some t.bv) (hkt : σ.kheap t.bv = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
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
      Inv (wakeSt3 σ1 t.bv x1 badge.bv) ∧ NSC Z.N Z.C σ1 ∧ ∀ dd pp, t.bv ∉ σ1.readyQueues dd pp := by
    intro σ1 x1 hc hk1 hin hrib
    obtain ⟨F1, hI1, -⟩ := post1 σ1 x1 hc hk1 hin hrib
    exact ⟨wake_inv3B hI1 hk1 hin hrib badge.bv, F1.nsc J.nsc, (hI1.notQueued hk1 (by rw [hin]; rfl)).1⟩
  refine WP.spec_mono (WP.spec_and (send_signal_bound_irelD J.ip hmb s a σ hI hn hk hidle hb hkt hrb badge hCR hA3)
    (P1.notification.send_signal.tinvF hAT s a n badge J.blk hnH (hNt n hnH))) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, s1, σ1, σd, σ', x1, hc, hk1, hin, hrib, hX1, hF1, hW1, hdon, hsend, hmw, hIR, hF2, hFS⟩,
    hbk⟩
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
  have hcur1 : CurInvR σ1 := fun e => F1.curInv (J.cur
    (hact1.elim (fun e1 => by rw [← e1]; exact e) (fun e1 => by rw [e1] at e; cases e)))
  have hrun1 : CurRunM σ1 := J.curRun.of_cn F1.curRunW hact1.symm
  obtain ⟨xn1, hkn1, -⟩ := F1.ntfnF hk
  have hoff1 : OffOK σ1 := F1.off J.off
  have hsp1 : ∀ c y k, σ1.kheap c = some (.schedContext y k) → y.scSporadic = true → Fl4Spec.scActive y = true := by
    intro c y k hc
    obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := F1.scB hc
    exact J.sv.scSpor c y0 k hy0
  obtain ⟨I', B', F2, AI', cur', run'⟩ := wake_specGR hI1 (wake_inv3B hI1 hk1 hin hrib badge.bv) hB1 hAI1 hcur1
    hrun1 hk1 (by rw [hin]; rfl) (wake_f3B hk1 hin badge.bv) hkn1 hoff1 hsp1 hdon hmw
  have FF : DWFr n.bv t.bv σ σ' := (DWFr.ofCFr F1).trans F2
  have hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    (hW1.trans (hFS.1.mono fun b hb => FinW.back hW1.1 (SzKeepC.of F1.szKeep) hb)).mono
      fun b h => h.elim id Or.inl
  have hRR : ∀ q ∈ Z.R, ∀ xr, σ.kheap q.bv = some (.reply xr) → xr.replyTcb = some t.bv →
      Detached Z.C Lst q ∧ L.mem s (rNextA q) = 0#u64 ∧ L.mem s (rPrevA q) = 0#u64 :=
    fun q hq xr hx' hxt => recvReplyHyp_holdsZR Z Ac Lst D s _ σ J q hq xr t.bv tcb hx' hxt hkt hrb
  have htD := J.not_dead_of_st htT hkt (by rw [hst]; simp [tsCode])
  obtain ⟨V', J'⟩ := J.wake_postD hIR (hF1.trans hF2) hw hbk hfoot FF I' B' AI' cur' run' hRR htD ⟨t, htT, rfl⟩
  exact ⟨σ', V', Ac, Lst, D, hsend, FF.sk.dt, J'⟩


end
end
end Fl4Proofs.P3
-- ===== from ScSignalJ
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
set_option maxHeartbeats 8000000 in
/-- **A badge-only signal keeps `JAtZR`** (module docstring): the spec's
outcome `updK σ n (.notification y)`, `y` the notification with a non-waiting
object (it was non-waiting), FL4's side `SingleRelI` at that outcome. -/
theorem JAtZR.signal_badge_post {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N)
    {x y : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hxw : ∀ l, x.ntfnObj ≠ .waitingNtfn l) (hyw : ∀ l, y.ntfnObj ≠ .waitingNtfn l)
    (hyb : y.ntfnBoundTcb = x.ntfnBoundTcb) (hys : y.ntfnSc = x.ntfnSc)
    {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hspec : spec = ({((), updK σ n.bv (.notification y))}, False))
    {s' : S} (hrel : SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ spec s')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s') :
    ∃ (σ' : Fl4Spec.State Unit) (V' : XVs), spec = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
  obtain ⟨σ3, hsp, hIR3, hNS, hW, -⟩ := hrel
  have e3 : σ3 = updK σ n.bv (.notification y) := by
    have h1 := (Prod.mk.inj (hsp.symm.trans hspec)).1
    exact congrArg Prod.snd (Set.singleton_injective h1)
  subst e3
  set σ3 := updK σ n.bv (.notification y) with hσ3
  -- the spec's frame
  have hN : NObj x.ntfnObj y.ntfnObj := Or.inr ⟨hxw, hyw⟩
  have F : NFr true n.bv σ σ3 := NFr.upd hk (Or.inr (Or.inr ⟨x, y, rfl, rfl, rfl, hN.queue, fun _ => hN,
    Or.inl hys, fun _ => hN, Or.inl hyb⟩))
  have hI3 : Inv σ3 := J.inv.updNtfn hk fun p hp => J.inv.ntfnSc n.bv x p hk (hys ▸ hp)
  -- FL4's side: `IRel` after
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT := hS.placed.tcb
  have h := hI.2
  have hSRT : SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c) s' σ3 :=
    ⟨h.1.stableN h.2.1.placed hW hNS, h.2.1.stable hW hNS, h.2.2.mono hW.1 (SzKeep.ntfnStep hNS)⟩
  have hI3' : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ3 := ⟨hIR3, hSRT⟩
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ3 := hSRT.2.1
  have hks : L.ksb s' = L.ksb s := hW.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    slotsSame_of_iw J.xtop.rel.1 J.xtop.rel.2.2.2.2.2.1 J.xtop.rel.2.2.2.2.2.2 hW
      fun b hb => Or.inl (NWrite.iwords hT hb)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3' hAR hSS F.sk.cdt F.sk.orig F.ksub hks
  have hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hW.mono fun b hb => NWrite.finW hT hb
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hw
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  -- core 0's debug word: no notification or TCB word
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk 0#u64 J.kern.cs0
    have hv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp)
    have hd88 : layout.node.DEBUG_TCBS.val = 88 := P1.debug_val
    refine hW.mem_eq J.kern.dwAl fun hb => ?_
    rcases NWrite.iwords (E := Z.E) (R := Z.R) (B := Z.B) hT hb with ⟨t, ht, g1, g2⟩ | ⟨e, he, g1, g2⟩ |
      ⟨r, hr, g1, g2⟩ | ⟨m, hm, g1, g2⟩ | ⟨wp, hwp, g1, g2⟩
    · have := J.kern.hnd t _ (J.zH.1 t ht) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd e _ (J.zH.2.1 e he) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd r _ (J.zH.2.2.1 r hr) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd m _ (J.zH.2.2.2 m hm) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.nodeB wp hwp 0#u64 (by simp); omega
  -- the scheduler fields
  have hAI3 : ActIdle σ3 := F.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_nfr F hS3 hIR3 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ3 := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.finW_irq hw) (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have R : JRestR (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ3 :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hSS hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.finW_utc hw hSS F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, hI3,
      fun e => F.curInv (J.cur (by rw [← (F.act rfl).1]; exact e)), F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa, F.isorted J.isorted,
      J.curRun.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curRunW, hblk⟩
  have hC0 := JCs.sameZR J hSS F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ3 := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨σ3, Z.vs, hspec, rfl, J.cs_frameI hks hX3 hw (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) F.szKeep hSS F.kback F.ipcFr hC R
    (dbgKeep_of_writes J.blk hW fun b hb => nwrite_notDbgB J.blk J.ip.e.tcb J.tcbs_eq.1 J.kern.heap J.zH.1 J.zH.2.2.2
      J.kern.hnd hb) F.sk.orig (XTopAt.idleW_eqS J.xtop hX3 F.sk.idle) J.zD⟩


variable (arI) in
/-- **The remote `RunningVM` signal on `JAtZR`** [J] (module docstring):
`SignalJHypZR`'s statement where `send_signal` finds the idle notification's
bound thread `RunningVM` (FL4's remote stall; VT-x, outside the spec model,
DESIGN §5, as `JVtHyps`). The waking cases (a waiting notification's head,
the bound thread blocked receiving, donating the notification's SC or not)
are proved (`JAtZR.signal_waitDJ`, `JAtZR.signal_boundDJ`, ScSignalDonJ). -/
def SignalRestJHypZR (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (n badge : U64) (x : Fl4Spec.Notification), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → n ∈ Z.N →
    σ.kheap n.bv = some (.notification x) →
    (x.ntfnObj = .idleNtfn ∧ ∃ t tcb, x.ntfnBoundTcb = some t ∧
      σ.kheap t = some (.tcb tcb) ∧ tcb.tcbState = .runningVM) →
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄

variable (arI) in
/-- **`SignalRestJHypZR` at the states satisfying `P`** (g3b; `P := True` is
`SignalRestJHypZR`; at `P := NativeScope` it holds outright). -/
def SignalRestJHypZRP (P : Fl4Spec.State Unit → Prop) (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (n badge : U64) (x : Fl4Spec.Notification), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → P σ → n ∈ Z.N →
    σ.kheap n.bv = some (.notification x) →
    (x.ntfnObj = .idleNtfn ∧ ∃ t tcb, x.ntfnBoundTcb = some t ∧
      σ.kheap t = some (.tcb tcb) ∧ tcb.tcbState = .runningVM) →
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄


set_option maxHeartbeats 8000000 in
/-- **`SignalJHypZR` from the waking signals' premise** (module docstring). -/
theorem signalJHyp_ofZR (hAT : P0.ArchTotal arI) (P : Fl4Spec.State Unit → Prop)
    (hW : SignalRestJHypZRP (L := L) arI P AR H Cs)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    SignalJHypZRP (L := L) arI P AR H Cs := by
  intro Z Ac Lst D s a σ n badge J hPσ hn
  obtain ⟨x, hk, hx⟩ := J.xtop.ipc.toN.ntfn n hn
  have hNt : ∀ m ∈ P1.Heap.ntfns H, H m = some .ntfn := fun _ h => h
  have hnH : n ∈ P1.Heap.ntfns H := J.zH.2.2.2 n hn
  have hP1 := P1.notification.send_signal.tinv hAT s a n badge J.blk hnH (hNt n hnH)
  -- the badge-only branches
  have post : ∀ (y : Fl4Spec.Notification), (∀ l, x.ntfnObj ≠ .waitingNtfn l) → (∀ l, y.ntfnObj ≠ .waitingNtfn l) →
      y.ntfnBoundTcb = x.ntfnBoundTcb → y.ntfnSc = x.ntfnSc →
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), updK σ n.bv (.notification y))}, False) →
      notification.send_signal st arI s a n badge ⦃ r => r.2 = a ∧
        SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ →
      notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
        (Lst' : U64 → List U64) (D' : Set U64),
        Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
        JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
    intro y hxw hyw hyb hys hspec hI
    refine WP.spec_mono (WP.spec_and hI hP1) ?_
    rintro ⟨s', a'⟩ ⟨⟨ea, hrel⟩, hb⟩
    try simp only [WP.uncurry'_pair] at hb
    subst ea
    obtain ⟨σ', V', h1, h2, J'⟩ := J.signal_badge_post hn hk hxw hyw hyb hys hspec hrel hb
    exact ⟨σ', V', Ac, Lst, D, h1, h2, J'⟩
  have hI := J.xtop.irelK J.ks J.buf
  cases ho : x.ntfnObj with
  | activeNtfn b0 =>
    exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn (Fl4Spec.combineNtfnBadges badge.bv b0)) x)
      (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
      (sendSignal_active_eq hk ho badge.bv) (send_signal_activeI (ar := arI) J.ip s a σ hI.1 hn hk ho badge)
  | waitingNtfn l =>
    exact J.signal_waitDJ hAT hmb hn hk ho badge
  | idleNtfn =>
    cases hb : x.ntfnBoundTcb with
    | none =>
      exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn badge.bv) x)
        (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
        (sendSignal_activate hk ho (Or.inl hb) badge.bv)
        (send_signal_idle_unboundI (ar := arI) J.ip s a σ hI.1 hn hk ho hb badge)
    | some t =>
      obtain ⟨hb0, hbt⟩ := Notif.optRef_some (hx.bound ▸ hb)
      obtain ⟨tcb, hkt, -⟩ := hI.1.tcb _ (hx.bound_mem hb0)
      rw [hbt] at hkt
      by_cases hrb : Fl4Spec.receiveBlocked tcb.tcbState = true
      · exact J.signal_boundDJ hAT hmb hn hk ho (t := L.mem s (nBoundA n)) (by rw [hbt]; exact hb)
          (by rw [hbt]; exact hkt) hrb
          badge
      by_cases hvm : tcb.tcbState = .runningVM
      · exact hW Z Ac Lst D s a σ n badge x J hPσ hn hk ⟨ho, t, tcb, hb, hkt, hvm⟩
      have hrb' : Fl4Spec.receiveBlocked tcb.tcbState = false := by simpa using hrb
      exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn badge.bv) x)
        (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
        (sendSignal_activate hk ho (Or.inr ⟨t, tcb, hb, hkt, hrb'⟩) badge.bv)
        (send_signal_idle_bound_idleI (ar := arI) J.ip s a σ hI.1 hn hk ho hb hkt hrb' hvm badge)



end
end
end Fl4Proofs.P3
-- ===== from XTopJointSchedRF
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}
/-- **`FpuOwnOK` [J] after FL4's TCB timers from `FpuOwnOK` at the entry**
(sch5 (A)): the timers keep the owner (`owF_fires`); the owner is a spec TCB at
entry, hence a related TCB (`JAtZR.obj`, ObjCover), and every related TCB is a
spec TCB after the timers (`NtfnStateRel.tcb`). -/
theorem fpuOwnOK_firesZR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ σ1 : Fl4Spec.State Unit} {m : U64 → U64}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hF : Fires σ σ1) (hN : NtfnStateRel Z.N Z.T m σ1)
    (hfo : FpuOwnOK σ) : FpuOwnOK σ1 := by
  intro o ho
  rw [owF_fires hF] at ho
  obtain ⟨x, hx⟩ := hfo o ho
  obtain ⟨t, ht, rfl⟩ := J.obj.tcb o x hx
  obtain ⟨y, hy, -⟩ := hN.tcb t ht
  exact ⟨y, hy⟩



end
end
end Fl4Proofs.P3
-- ===== from XTopJointSchedRF2
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}
/-- **`NdOK` after FL4's TCB timers** (module docstring). -/
theorem JAtZR.ndOK_fire {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hNd : NdOK (L := L) s σ) {s1 : S}
    (hf : P1.FootD st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1)
    (hF : Fires σ σ1) : NdOK (L := L) s1 σ1 := by
  have hkf := J.kern.ksbFit
  have hka := J.kern.ksbAl
  have hks := J.kern.hks
  have hH := J.kern.heap
  have hKW := J.kwApartJ (s' := s) rfl (fun c hc => J.blk.2.2.1.2.2.tm.npl c hc)
  obtain ⟨hdl, hdi, hds⟩ := fires_dom hF
  refine hNd.keep hf.1 (fun o ho h8 => hf.mem_eq (ksW_al hkf hka ho h8) fun hb => ?_) hdl hdi hds
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  rcases hb with hb | hb
  · rcases hKW _ (ksW_al hkf hka ho h8) hb with e | e <;> rw [hv] at e <;> omega
  · rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
    · have hy' : H y = some .tcb := hy
      have hfit := hH.fits y _ hy'
      simp only [P1.HKind.bits] at hfit
      have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12] at hfit
      have hdv : (P1.dnA y).val = y.val + 3576 := by
        unfold P1.dnA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have h3 := hks y .tcb hy' (fun z h => by cases h)
      simp only [P1.HKind.bits, h12] at h3
      have := congrArg UScalar.val e
      rw [hv, hdv] at this
      omega
    · have hy' : H y = some .tcb := hy
      have hfit := hH.fits y _ hy'
      simp only [P1.HKind.bits] at hfit
      have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12] at hfit
      have hdv : (P1.dpA y).val = y.val + 3584 := by
        unfold P1.dpA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have h3 := hks y .tcb hy' (fun z h => by cases h)
      simp only [P1.HKind.bits, h12] at h3
      have := congrArg UScalar.val e
      rw [hv, hdv] at this
      omega
    · have hnv := P1.nodeAt_val (J.blk.2.2.1.2.2.tm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp)
      unfold P1.LawfulStore.nodeBase at hnv
      have := congrArg UScalar.val e
      rw [hv, hnv] at this
      simp [layout.node.DEBUG_TCBS] at this
      omega



set_option maxHeartbeats 2000000 in
/-- **FL4's `schedule` from `JAtZR`, with the domain switch, up to the FPU**
(module docstring): no `σ.domainTime ≠ 0`; instead `σ.domainTime ≠ 0 ∨
NdOK s σ` (NdOK's [J] facts at the entry), `ArchNdF` [P] and `FpuOwnOK σ`
[J] at the entry. -/
theorem jat_scheduleWP0FZR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI) (P : Fl4Spec.State Unit → Prop)
    (hP : ∀ σ1, Fires σ σ1 → P σ1) (hSig : SignalJHypZRP (L := L) arI P AR H Cs)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' ∧ NtfnStateRel Z.N Z.T (L.mem r.1) σ' ∧ NSC Z.N Z.C σ' ∧ Inv σ' ∧
      CurInv σ' ∧ ActIdle σ' ∧ ∃ rf : S × A,
        ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
          JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 rf.1 rf.2 σ1) ∧
          timer.fire st arI s a = ok rf ∧ L.ksb rf.1 = L.ksb s ∧ FpuOwnOK σ1) ∧
        P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) ∧
        ∃ σ3 : Fl4Spec.State Unit, OffOK σ3 ∧ (RunM σ1 → RunW σ3) ∧
          Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hB := J.blk
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hfire : timer.fire st arI s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1 ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1 ∧ NSC Z.N Z.C σ1 ∧ SchedPreW0R Z.T Z.C σ1 ∧
      ((σ1.domainTime ≠ 0 ∨ NdOK (L := L) r.1 σ1) ∧
        (∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb r.1).val ∨ (L.ksb r.1).val + 13568 ≤ n.val) ∧
        ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
          JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 r.1 r.2 σ1) ∧
          timer.fire st arI s a = ok r ∧ L.ksb r.1 = L.ksb s ∧ FpuOwnOK σ1)) ⦄ := by
    refine WP.spec_mono (P1.spec_eq' (WP.spec_and (J.fireJ P hP hSig) (P1.timer.fire.kw hAT hNt s a hB))) ?_
    rintro ⟨s1, a1⟩ ⟨hf, ⟨σ1, V1, Ac1, Lst1, D1, h1, hd1, J1⟩, hk⟩
    simp only [WP.uncurry'_pair] at hk
    exact ⟨σ1, h1, J1.xtop.fin.1.1.1, J1.xtop.fin.1.1.2.2.1, J1.nsc, ⟨J1.inv, J1.cur, J1.off, J1.act, J1.own⟩,
      hd.imp (fun h => by rw [hd1]; exact h) (fun h => J.ndOK_fire h hk h1), J1.nk,
      ⟨V1, Ac1, Lst1, D1, J1⟩, hf, hk.1, fpuOwnOK_firesZR J h1 J1.xtop.fin.1.1.2.2.1 hFO⟩
  exact schedule_refinesWP0FR s a σ hS hR J.nsc hnd hfire (fun _ _ h => h.2.2.2) hA hAN hsni hsend hT


end
end
end Fl4Proofs.P3
-- ===== from XTopJointSchedRF3
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}
/-- **`JAtZR` at the fake state** (module docstring). -/
theorem JAtZR.ndFJ {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (v16 v24 v40 : U64) (di : Nat) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZR (L := L) arI AR Z H Cs Ac' Lst' D' (ndF (L := L) s (L.ksb s) v16 v24 v40) a (ndFSt σ v16.bv di) := by
  have hkf := J.kern.ksbFit
  have hka := J.kern.ksbAl
  obtain ⟨Ac1, Lst1, D1, J1⟩ := J.schedJ (schedStep_dom2 Z.th s σ v16 v24 di rfl hkf hka)
  obtain ⟨Ac2, Lst2, J2⟩ := J1.workUnitsJD (arI := arI) v40
  have e : core.num.U64.wrapping_add (L.ksb (ndF2 (L := L) s (L.ksb s) v16 v24)) layout.ks.WORK_UNITS =
      ksW (L.ksb s) 40#u64 := by
    simp only [ndF2, P1.LawfulStore.ksb_wr, ksW]
    unfold layout.ks.WORK_UNITS; rfl
  rw [e] at J2
  exact ⟨Ac2, Lst2, D1, J2⟩


set_option maxHeartbeats 2000000 in
/-- **`JAtZR.sch_tail` from the spec step's facts** instead of `schedule σ =
{σ'}` (module docstring). -/
theorem JAtZR.sch_tailS {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {Ac' : Set U64}
    (hSch : SchS σ σ') (hik : σ'.idleThread = σ.idleThread ∧ σ'.idleSc = σ.idleSc)
    (hw : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ))
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hR' : NtfnStateRel Z.N Z.T (L.mem s') σ') (hN' : NSC Z.N Z.C σ')
    (hI' : Inv σ') (hC' : CurInv σ') (hA' : ActIdle σ') (hcr : CurRunW σ') (hoff : Sched.OffOK σ')
    (hbsa : Sched.BlockedScActive σ')
    (hT : SchTailHyps (L := L) AR Z H Cs D s s' a' σ' Ac') :
    ∃ Lst' : U64 → List U64, JAtZR (L := L) arI AR Z H Cs Ac' Lst' D s' a' σ' := by
  have hK : SchStep (fun _ => False) σ σ' := hSch.1
  have hKc : ∀ ct : Fl4Spec.ObjRef, SchStep (fun p => p = ct) σ σ' := fun ct =>
    { hK with kh := fun p => (hK.kh p).mono False.elim }
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hS := J.xtop.fin.1.1.1
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sched_step J.xtop J.ip J.nk hwT (hKc σ.curThread) hS' hR' hT.curOK hT.ar
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hSch.2⟩
  refine ⟨Lst', J.sch_frame hwT hK hX' hCR' hRF' hY' hM' (J.sch_buf hwT hK) hRP' (J.sch_apart hwT hK)
    (J.sch_jpl hwT hK (J.idleW_keep hS' hik.1 hik.2).2) (J.sc_jcov hwT hT.dead (fun q hq hn => absurd hq hn)
      (J.idleW_keep hS' hik.1 hik.2))
    (J.sch_kern hwT hK hS' hT.dbg hT.dwNe (J.sch_csc hwT hK hS' hI' hC' hT.dead).1) (J.sch_utc hwT hK hT.dbg) hN' hI' (Or.inr hC')
    (Or.inl (curOwn_of_curInv hS' hI' hC')) hoff hA' hbsa (Or.inr hcr) hT.blk hT.dbgK (J.idleW_keep hS' hik.1 hik.2).1 J.zD⟩


set_option maxHeartbeats 4000000 in
/-- **FL4's `schedule` refines the spec's at `J`, with the domain switch**
(module docstring): `jat_scheduleFRF` without `σ.domainTime ≠ 0`. -/
theorem jat_scheduleFR2ZR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (P : Fl4Spec.State Unit → Prop) (hP : ∀ σ1, Fires σ σ1 → P σ1) (hSig : SignalJHypZRP (L := L) arI P AR H Cs)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ := by
  have h0Cs : 0#u64 ∈ Cs := J.kern.cs0
  have hB := J.blk
  obtain ⟨⟨Q, R, hq⟩, hBd, hXi, hSc, hSg⟩ := id hB
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    P1.nodeAt_aligned (hq.nodes 0#u64 h0Cs) (by simp) (by simp)
  refine WP.spec_mono (WP.spec_and (WP.spec_and
    (jat_scheduleWP0FZR s a σ J hd hnd hAT P hP hSig hA hAN hFO hsni hsend hT)
    (P1.sched.schedule.kw hAT hNt s a hB)) (WP.spec_and (P1.sched.schedule.tinv hAT hNt s a Q R hq hBd hSc hXi hSg)
      hTail)) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA', rf, ⟨⟨V1, Ac1, Lst1, D1, J1⟩, hfr, hkf, -⟩, hw, hrun⟩,
    hkw⟩, ⟨htinv, hRest⟩⟩
  simp only [WP.uncurry'_pair] at hkw htinv
  obtain ⟨rf', hrf', -, hkw⟩ := hkw
  obtain rfl : rf = rf' := by simpa using (hrf'.symm.trans hfr).symm
  have hTl := hRest rf σ1 σ' D1 hF hsc hw hS' hI' hC' hA'
  obtain ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', -, -, -, -⟩ := htinv
  -- the fake pre-state
  have hkf1 := J1.kern.ksbFit
  have hka1 := J1.kern.ksbAl
  set kb := L.ksb rf.1 with hkb
  set s0 := ndF (L := L) rf.1 kb (L.mem s' (ksW kb 16#u64)) (L.mem s' (ksW kb 24#u64)) (L.mem s' (ksW kb 40#u64))
    with hs0
  set σ0 := ndFSt σ1 (L.mem s' (ksW kb 16#u64)).bv σ'.domainIndex with hσ0
  obtain ⟨Ac0, Lst0, D0, J0⟩ := J1.ndFJ (L.mem s' (ksW kb 16#u64)) (L.mem s' (ksW kb 24#u64))
    (L.mem s' (ksW kb 40#u64)) σ'.domainIndex
  have hw0 : P1.WritesIn st s0 s' (KFoot st Z.T Z.N Z.C Z.c s0 σ0) := ndF_writes σ'.domainIndex hkf1 hka1 hw
  have hk0 : L.ksb s0 = L.ksb rf.1 := ndF_ksb _ _ _ _ _
  have hks' : L.ksb s' = L.ksb s := hkw.1.trans hkf
  have hnA : L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb (hk0.trans hkf) _ _
  have hnA1 : L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb hkf _ _
  have hN0 := hq.nodes 0#u64 h0Cs
  have hdv : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s 0#u64 + 88 := by
    rw [P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp), P1.debug_val]
  have hdbg0 : L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem rf.1 (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) := by
    rw [hnA, hnA1, hs0]
    refine ndF_mem_ne _ _ _ _ hkf1 hka1 hal fun hb => ?_
    have h16 := ksW_val (kb := kb) (o := 16#u64) (by simp; omega)
    have h24 := ksW_val (kb := kb) (o := 24#u64) (by simp; omega)
    have h40 := ksW_val (kb := kb) (o := 40#u64) (by simp; omega)
    have hkbs : kb.val = (L.ksb s).val := by rw [hkf]
    unfold P1.LawfulStore.nodeBase at hdv
    rcases hb with e | e | e <;> have := congrArg UScalar.val e <;> simp at h16 h24 h40 <;> omega
  have hdbg : L.mem s' (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [hdbg0, P1.nodeAt_of_ksb hk0]
    exact hkw.mem_eq (by rw [hnA1]; exact hal) (P1.dbg0_not_schedW J1.blk h0Cs)
  have hdw : (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val := by
    have hN0' := hq'.nodes 0#u64 h0Cs
    have hct : L.curW s' ∈ P1.Heap.tcbs H := hq'.curT
    have hv := P1.nodeAt_val hN0' (off := layout.node.DEBUG_TCBS) (by simp)
    have hsv := P1.field_val (hq'.tcbs _ hct) (K := 3328#u64) (by decide)
    have hdj := hN0'.disj _ hct
    have hv' : (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s' 0#u64 + 88 := by
      rw [hnA, ← P1.nodeAt_of_ksb hks' 0#u64 layout.node.DEBUG_TCBS, hv, P1.debug_val]
    have hsv' : (P1.stA (L.curW s')).val = (L.curW s').val + 3328 := by
      rw [P1.stA_eq, hsv]; rfl
    rw [hv', hsv']
    have e12 : (2 : Nat) ^ 12 = 4096 := rfl
    rw [e12] at hdj
    omega
  obtain ⟨σ3, ho3, hr3, he3⟩ := hrun
  have hSch1 : SchS σ1 σ' := schs_schedule.of_eq hsc
  have hSch0 : SchS σ0 σ' := SchS.ndF hSch1 _ _
  have hK1 : SchStep (fun _ => False) σ0 σ' := hSch0.1
  have hL1 : LK (fun _ => False) σ0 σ' := lkm_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hik : σ'.idleThread = σ0.idleThread ∧ σ'.idleSc = σ0.idleSc :=
    ik_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hwT := WritesIn.tfoot_of_kfoot hw0
  have hSS : SlotsSame Z.th (L.mem s0) (L.mem s') :=
    slotsSame_of_iw J0.xtop.rel.1 J0.xtop.rel.2.2.2.2.2.1 J0.xtop.rel.2.2.2.2.2.2 hwT
      fun b hb => tfoot_iw J0.xtop.fin.1.1.1 hb
  obtain ⟨Qc, Rc, hcc, hsc'⟩ := hS'.lists
  obtain ⟨hth, hvt⟩ := hVt _ _ _ _ _ _ _ J0 _ hcc.curT
  have hcur : Vs.CurOK st Z.th s' σ' :=
    ⟨_, hsc'.curThread.symm, hth, fun p asid h => hvt p asid (by
      rwa [hSS.capAt ⟨_, 1, Or.inr ⟨hth, by decide⟩, rfl⟩] at h)⟩
  have hX' : XTopAt (L := L) AR (Z.mv Z.G V1) s' a' σ' :=
    xtop_sched_step J0.xtop J0.ip J0.nk hwT (ct := σ0.curThread)
      { hK1 with kh := fun p => (hK1.kh p).mono False.elim } hS' hR' hcur hTl.ar
  have hSOK0 := hSch0.2
  have hY1 : YieldRel Z.T Z.C (L.mem s') σ' :=
    (ScAll.of_k J0.xtop.fin.1.1.1 J0.rp J0.yld J0.mcp J0.call J0.rfree ⟨⟨hS', hR', hN', hI'⟩, hw0, hSOK0⟩).2.1
  have hdead : ∀ q ∈ D0, Sched.DeadP (L := L) H s' q := fun q hq =>
    J0.deadP_sch_step hX' hwT hK1 hL1 hA' (J0.ymd hS' hY1 ((hSOK0.ykeep rfl).dk q.bv)) (fun h => h)
      (J0.jcov.dead q hq)
  -- every debug word kept from the fake pre-state (`ndF` writes kernel-state words only)
  have hdk0 : P1.DbgKeep st (P1.Heap.tcbs H) Cs s0 s' := by
    have h1 := P1.dbgKeep_schedW J1.blk J1.kern.ksbFit hkw
    obtain ⟨⟨Qk, Rk, hqk⟩, -⟩ := J1.blk
    refine ⟨hkw.1.trans hk0.symm, fun b hb => ?_⟩
    have hb1 : P1.DbgW st (P1.Heap.tcbs H) Cs rf.1 b := P1.DbgW.ksb hk0 hb
    rw [h1.2 b hb1]
    refine (ndF_mem_ne _ _ _ _ hkf1 hka1 (P1.dbgW_aligned J1.blk hb1) fun hn => ?_).symm
    have h16 := ksW_val (kb := kb) (o := 16#u64) (by simp; omega)
    have h24 := ksW_val (kb := kb) (o := 24#u64) (by simp; omega)
    have h40 := ksW_val (kb := kb) (o := 40#u64) (by simp; omega)
    simp at h16 h24 h40
    have hbv : b.val = kb.val + 16 ∨ b.val = kb.val + 24 ∨ b.val = kb.val + 40 := by
      rcases hn with e | e | e <;> rw [e] <;> omega
    rcases hb1 with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
    · have hv := P1.field_val (hqk.tcbs y hy) (K := 3576#u64) (by simp)
      have ho := hqk.ksOut y hy
      rw [← hkb] at ho
      have h35 : (3576#u64 : U64).val = 3576 := by simp
      have e' : b.val = y.val + 3576 := by
        rw [e, show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, hv, h35]
      simp only [Nat.reducePow] at ho
      omega
    · have hv := P1.field_val (hqk.tcbs y hy) (K := 3584#u64) (by simp)
      have ho := hqk.ksOut y hy
      rw [← hkb] at ho
      have h35 : (3584#u64 : U64).val = 3584 := by simp
      have e' : b.val = y.val + 3584 := by
        rw [e, show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, hv, h35]
      simp only [Nat.reducePow] at ho
      omega
    · have hN := hqk.nodes c hc
      have hv : b.val = L.nodeBase rf.1 c + 88 := by
        rw [e, P1.nodeAt_val hN (off := layout.node.DEBUG_TCBS) (by simp), P1.debug_val]
      have hnb : L.nodeBase rf.1 c = (L.ksb rf.1).val + 13568 + c.val * 4288 := rfl
      rw [← hkb] at hnb
      omega
  have hT2 : SchTailHyps (L := L) AR (Z.mv Z.G V1) H Cs D0 s0 s' a' σ' Ac :=
    ⟨hcur, hTl.ar, hdbg, hdw, hdead,
      ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', hSg.ksb' hks'⟩, hdk0⟩
  obtain ⟨Lst', J'⟩ := J0.sch_tailS hSch0 hik hw0 hS' hR' hN' hI' hC' hA' (RunW.scAndTimer (hr3 J1.curRun) he3)
    (OffOK.scAndTimer ho3 he3) (bsa_schedule J1.bsa hsc) hT2
  exact ⟨σ1, σ', hF, hsc, ⟨J'.xtop.relTop, _, _, _, _, _, _, J'.toJ (Or.inr hC')⟩, ⟨V1, Ac, Lst', D0, J'⟩, hC',
    RunW.scAndTimer (hr3 J1.curRun) he3⟩


/-- **`jat_scheduleFR2ZR` with `SignalJHypZR` reduced to the waking signals**
(`signalJHyp_ofZR`, as `jat_scheduleSRF`), at the states satisfying `P` (g3b). -/
theorem jat_scheduleSR2ZRP {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (P : Fl4Spec.State Unit → Prop) (hP : ∀ σ1, Fires σ σ1 → P σ1)
    (hW : SignalRestJHypZRP (L := L) arI P AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ :=
  jat_scheduleFR2ZR s a σ J hd hnd hAT hVt P hP (signalJHyp_ofZR hAT P hW hmb) hA hAN hFO hsni hsend hT hTail

/-- **`jat_scheduleFR2ZR` with `SignalJHypZR` reduced to the waking signals**
(`jat_scheduleSR2ZRP` at `P := True`, the pre-g3b statement). -/
theorem jat_scheduleSR2ZR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hW : SignalRestJHypZR (L := L) arI AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ :=
  jat_scheduleSR2ZRP s a σ J hd hnd hAT hVt (fun _ => True) (fun _ _ => trivial)
    (fun Z1 Ac1 Lst1 D1 s1 a1 σ1 n1 b1 x1 J1 _ hn hk hb => hW Z1 Ac1 Lst1 D1 s1 a1 σ1 n1 b1 x1 J1 hn hk hb) hmb
    hA hAN hFO hsni hsend hT hTail


end
end
end Fl4Proofs.P3
