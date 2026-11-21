/-
P1: **the reset keeps the invariants** (`ResetP1Step`): the untyped region's
objects are dropped at the start (`BlkOK.drop`); then the reset clears the
region (untracked words of the dropped heap), rewrites the untyped cap's
slot (cap-slot words, or untracked ones if the slot was in a dropped object)
and passes preemption points (`preemption_point.pp`), keeping `BlkOK` over
the dropped heap, the dead objects dead and the current thread's words.
-/
import Fl4Proofs.P1.QueueRetype
import Fl4Proofs.P1.QueueHeapFree
import Fl4Proofs.P1.QueueKeeps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {D : U64 → Prop} {Cs : Set U64} {s : S}

/-- A word in no kept object and off the nodes is untracked over the dropped heap. -/
theorem untracked_of_noKept (hH : HeapOK H) {s1 : S} {b : U64} (ha : Aligned b)
    (hnk : ∀ q k, H.drop D q = some k → ¬ InObj q k b)
    (hnode : ∀ c ∈ Cs, b.val < L.nodeBase s1 c ∨ L.nodeBase s1 c + 4288 ≤ b.val) :
    Untracked st (H.drop D).tcbs Cs (H.drop D) (H.drop D).frame s1 b := by
  refine ⟨⟨ha, fun t ht => ?_, hnode⟩, fun e he => ?_, fun hs => ?_⟩
  · have := hnk t .tcb ht
    simp only [InObj, HKind.bits, not_and, not_lt] at this
    by_cases h1 : t.val ≤ b.val
    · exact Or.inr (this h1)
    · exact Or.inl (by omega)
  · have hb8 : b.val % 8 = 0 := ha
    rcases he with he | he
    · have hal := hH.align e .ep (Heap.drop_eq_some.1 he).2
      have := hnk e .ep he
      simp only [InObj, HKind.bits, not_and, not_lt] at this hal
      by_cases h1 : e.val ≤ b.val
      · exact Or.inr (this h1)
      · exact Or.inl (by omega)
    · have hal := hH.align e .ntfn (Heap.drop_eq_some.1 he).2
      have := hnk e .ntfn he
      simp only [InObj, HKind.bits, not_and, not_lt] at this hal
      by_cases h1 : e.val ≤ b.val
      · have := this h1; exact Or.inr (by omega)
      · exact Or.inl (by omega)
  · obtain ⟨-, p, k, hp, -, hin⟩ := hs
    exact hnk p k hp hin

/-- A word of a dropped object is in no kept object. -/
theorem noKept_of_dropped (P : DropOK st H D Cs s) {q : U64} {k : HKind} (hq : H q = some k) (hD : D q)
    {b : U64} (hin : InObj q k b) : ∀ q' k', H.drop D q' = some k' → ¬ InObj q' k' b := fun q' k' hq' hin' => by
  obtain ⟨hD', hq''⟩ := Heap.drop_eq_some.1 hq'
  exact offDrop_of_obj P.heap hq'' hD' hin' q k hq hD hin

/-- A word of a dropped object is off the nodes. -/
theorem nodeOff_of_dropped (P : DropOK st H D Cs s) {q : U64} {k : HKind} (hq : H q = some k) (hD : D q)
    {b : U64} (hin : InObj q k b) : ∀ c ∈ Cs, b.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val :=
  fun c hc => by
    by_contra hn
    simp only [not_or, not_lt] at hn
    exact P.nodes c hc b hn.1 (by omega) q k hq hD hin

/-- A word of a dropped object is untracked over the dropped heap. -/
theorem untracked_of_dropped (P : DropOK st H D Cs s) {s1 : S} (hk : L.ksb s1 = L.ksb s) {q : U64} {k : HKind}
    (hq : H q = some k) (hD : D q) {b : U64} (ha : Aligned b) (hin : InObj q k b) :
    Untracked st (H.drop D).tcbs Cs (H.drop D) (H.drop D).frame s1 b :=
  untracked_of_noKept P.heap ha (noKept_of_dropped P hq hD hin) fun c hc => by
    have e : L.nodeBase s1 c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
    rw [e]; exact nodeOff_of_dropped P hq hD hin c hc

/-- A word of the region is in no kept object. -/
theorem noKept_of_region {lo hi : Nat} {b : U64} (h1 : lo ≤ b.val) (h2 : b.val < hi) :
    ∀ q k, H.drop (RegionD H lo hi) q = some k → ¬ InObj q k b := fun q k hq hin => by
  obtain ⟨hD, hq'⟩ := Heap.drop_eq_some.1 hq
  apply hD
  simp only [RegionD, hq', Option.elim, MeetsR]
  have := hin.1; have := hin.2
  omega

/-- A cap-slot word over `H` is a cap-slot word over the dropped heap, or an
untracked one (if it was in a dropped object). -/
theorem capw_drop (P : DropOK st H D Cs s) {s1 : S} (hks : L.ksb s1 = L.ksb s) {b : U64} (ha : Aligned b)
    (hw : CapW H.tcbs H.omega H.frame b) :
    CapW (H.drop D).tcbs (H.drop D).omega (H.drop D).frame b ∨
      Untracked st (H.drop D).tcbs Cs (H.drop D) (H.drop D).frame s1 b := by
  rcases hw with ⟨t, ht, K, hK, rfl⟩ | ⟨⟨ha', p, k, hp, hk, hin⟩, hn⟩
  · by_cases hD : D t
    · have hal := P.heap.align t .tcb ht
      have hfit := P.heap.fits t .tcb ht
      have hv : (core.num.U64.wrapping_add t K).val = t.val + K.val := by
        simp only [HKind.bits] at hfit
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      exact Or.inr (untracked_of_dropped P hks ht hD ha ⟨by omega, by simp only [HKind.bits]; omega⟩)
    · exact Or.inl (Or.inl ⟨t, Heap.mem_tcbs_drop.2 ⟨ht, hD⟩, K, hK, rfl⟩)
  · by_cases hD : D p
    · exact Or.inr (untracked_of_dropped P hks hp hD ha hin)
    · exact Or.inl (Or.inr ⟨⟨ha', p, k, Heap.drop_eq_some.2 ⟨hD, hp⟩, hk, hin⟩,
        fun h => hn (Heap.frame_drop_sub h)⟩)

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **Writes of cap-slot or untracked words keep `BlkOK`** (with `blk_of_capw`'s frames). -/
theorem blk_of_capw_untracked {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b ∨ Untracked st T Cs H Sg s b) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ PFr st T Sg s s' ∧
      L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.actionW s' = L.actionW s ∧
      (∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
      (∀ b ∈ Sg, L.mem s' b = L.mem s b) := by
  have hw' := h.widen (U := {b | B b ∧ Untracked st T Cs H Sg s b}) fun a ha => ha.2
  obtain ⟨h1, rest⟩ := blk_of_capw hw' hw fun b hb => by
    rcases hB b hb with (hl | ⟨hm, hn⟩) | hu
    · exact Or.inl hl
    · exact Or.inr ⟨Or.inl hm, hn⟩
    · exact Or.inr ⟨Or.inr ⟨hb, hu⟩, hu.sg⟩
  refine ⟨h1.narrow (fun o ho h8 => by rw [hw.1]; exact h.2.2.2.2.ksΩ o ho h8)
    (fun c hc b ha hin => h.2.2.1.1.scW c hc b ha hin) h.2.2.2.2.sub, rest⟩

end


/-! ## The reset's invariant -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {D : U64 → Prop} {Cs : Set U64}

/-- **Along the reset**, from its start `s0`: `BlkOK` over the dropped heap,
the dead kept objects dead, the current thread's words, the base and core. -/
structure RInv (st : machine.Store S) [L : LawfulStore st] (H : Heap) (D : U64 → Prop) (Cs : Set U64)
    (s0 s1 : S) : Prop where
  blk : ∃ Ac', BlkOK st (H.drop D).tcbs Cs (H.drop D).omega (H.drop D) (H.drop D).frame (H.drop D).replies
    (H.drop D).scs (H.drop D).ntfns (H.drop D).scBits Ac' s1
  dead : ∀ q, H.drop D q = H q → DeadQ st H s0 q → DeadQ st (H.drop D) s1 q
  keep : ResetKeeps st s0 s1
  ksb : L.ksb s1 = L.ksb s0
  cpu : L.cpu s1 = L.cpu s0

theorem epTSA_val' {e : U64} (h : e.val + 16 ≤ 2 ^ 64) : (epTSA e).val = e.val + 8 := by
  unfold epTSA
  have : layout.ep.TAIL_STATE.val = 8 := by unfold layout.ep.TAIL_STATE; rfl
  rw [core.num.U64.wrapping_add_val_eq, this]
  simp [U64.size_def, U64.numBits]; omega

/-- A dead object stays dead when the words `DeadQ` reads are kept. -/
theorem DeadQ.keepw {H' : Heap} {s1 s2 : S} {q : U64} (h : DeadQ st H' s1 q)
    (ht : H' q = some .tcb → L.mem s2 (stA q) = L.mem s1 (stA q) ∧ L.mem s2 (scA q) = L.mem s1 (scA q) ∧
      L.mem s2 (boundA q) = L.mem s1 (boundA q) ∧ L.mem s2 (yieldA q) = L.mem s1 (yieldA q))
    (ha : L.actionW s2 = L.actionW s1) (hi : L.idleW s2 = L.idleW s1)
    (he : H' q = some .ep ∨ H' q = some .ntfn → L.epState s2 q = L.epState s1 q)
    (hn : H' q = some .ntfn → L.mem s2 (ntfnBtA q) = L.mem s1 (ntfnBtA q) ∧
      L.mem s2 (ntfnScA q) = L.mem s1 (ntfnScA q))
    (hr : H' q = some .reply → L.mem s2 (rTcbA q) = L.mem s1 (rTcbA q))
    (hs : ∀ z, H' q = some (.sc z) → L.mem s2 (scTcbA q) = L.mem s1 (scTcbA q) ∧
      L.mem s2 (scReplyA q) = L.mem s1 (scReplyA q) ∧ L.mem s2 (scNtfnA q) = L.mem s1 (scNtfnA q) ∧
      L.mem s2 (scYieldFromA q) = L.mem s1 (scYieldFromA q)) :
    DeadQ st H' s2 q := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := h
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_, fun z hq => ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := ht hq
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := d1 hq
    exact ⟨e1 ▸ a1, e2 ▸ a2, e3 ▸ a3, ha ▸ a4, hi ▸ a5, e4 ▸ a6⟩
  · rw [he (Or.inl hq)]; exact d2 hq
  · obtain ⟨e1, e2⟩ := hn hq
    obtain ⟨a1, a2, a3⟩ := d3 hq
    exact ⟨by rw [he (Or.inr hq)]; exact a1, e1 ▸ a2, e2 ▸ a3⟩
  · rw [hr hq]; exact d4 hq
  · obtain ⟨e1, e2, e3, e4⟩ := hs z hq
    obtain ⟨a1, a2, a3, a4⟩ := d5 z hq
    exact ⟨e1 ▸ a1, e2 ▸ a2, e3 ▸ a3, e4 ▸ a4⟩

/-- **A step of the reset keeps `RInv`**, given `BlkOK` after and the frames:
the kept TCBs' fields from 192, the scheduler words, the kept endpoints'
state words and the frame words. -/
theorem RInv.step {s0 s1 s2 : S} (I : RInv st H D Cs s0 s1) {Ac2 : Set U64}
    (hb2 : BlkOK st (H.drop D).tcbs Cs (H.drop D).omega (H.drop D) (H.drop D).frame (H.drop D).replies
      (H.drop D).scs (H.drop D).ntfns (H.drop D).scBits Ac2 s2)
    (fld : ∀ y ∈ (H.drop D).tcbs, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K))
    (ec : L.curW s2 = L.curW s1) (ecs : L.cscW s2 = L.cscW s1) (ea : L.actionW s2 = L.actionW s1)
    (ei : L.idleW s2 = L.idleW s1)
    (hep : ∀ e, H.drop D e = some .ep ∨ H.drop D e = some .ntfn → L.mem s2 (epTSA e) = L.mem s1 (epTSA e))
    (sig : ∀ b ∈ (H.drop D).frame, L.mem s2 b = L.mem s1 b)
    (hk : L.ksb s2 = L.ksb s1) (hc : L.cpu s2 = L.cpu s1) : RInv st H D Cs s0 s2 := by
  obtain ⟨Ac1, hb1⟩ := I.blk
  have hO := hb1.2.2.1.1
  have tf : ∀ {q : U64}, H.drop D q = some .tcb → L.mem s2 (stA q) = L.mem s1 (stA q) ∧
      L.mem s2 (scA q) = L.mem s1 (scA q) ∧ L.mem s2 (boundA q) = L.mem s1 (boundA q) ∧
      L.mem s2 (yieldA q) = L.mem s1 (yieldA q) := fun hq =>
    ⟨by rw [stA_eq]; exact fld _ hq _ (by simp) (by simp) (by simp),
     by rw [scA_eq]; exact fld _ hq _ (by simp) (by simp) (by simp),
     by unfold boundA; exact fld _ hq _ (by simp) (by simp) (by simp),
     by unfold yieldA; exact fld _ hq _ (by simp) (by simp) (by simp)⟩
  refine ⟨⟨Ac2, hb2⟩, fun q hq hd => (I.dead q hq hd).keepw tf ea ei (fun h' => by
      unfold LawfulStore.epState; rw [hep q h']) (fun h' => ⟨sig _ (hO.ntB q h').2, sig _ (hO.ntW q h')⟩)
      (fun h' => sig _ (hO.tcbW h'))
      (fun z h' => ⟨sig _ (hO.fixW q ⟨z, h'⟩).1, sig _ (hO.repW q ⟨z, h'⟩), sig _ (hO.snW q ⟨z, h'⟩),
        sig _ (hO.syW q ⟨z, h'⟩)⟩),
    ?_, hk.trans I.ksb, hc.trans I.cpu⟩
  obtain ⟨k1, k2, k3, k4, k5⟩ := I.keep
  have hcT : L.curW s0 ∈ (H.drop D).tcbs := by rw [← k1]; exact hb1.1.choose_spec.choose_spec.curT
  obtain ⟨t1, t2, -, -⟩ := tf hcT
  exact ⟨ec.trans k1, ecs.trans k2, ea.trans k3, t2.trans k4, t1.trans k5⟩

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {D : U64 → Prop} {Cs : Set U64}

/-- A kept endpoint's or notification's state word is no cap-slot or untracked word. -/
theorem ep_not_written (hH : HeapOK H) {s1 : S} {e : U64}
    (he : H.drop D e = some .ep ∨ H.drop D e = some .ntfn) {b : U64}
    (hb : CapW (H.drop D).tcbs (H.drop D).omega (H.drop D).frame b ∨
      Untracked st (H.drop D).tcbs Cs (H.drop D) (H.drop D).frame s1 b)
    (hbe : b = epTSA e) : False := by
  obtain ⟨k, hek, hk⟩ : ∃ k, H e = some k ∧ (k = .ep ∨ k = .ntfn) := by
    rcases he with he | he
    · exact ⟨_, (Heap.drop_eq_some.1 he).2, Or.inl rfl⟩
    · exact ⟨_, (Heap.drop_eq_some.1 he).2, Or.inr rfl⟩
  have hfit := hH.fits e k hek
  have hal := hH.align e k hek
  have hb4 : 4 ≤ k.bits := by rcases hk with rfl | rfl <;> simp [HKind.bits]
  have h16 : 16 ≤ 2 ^ k.bits := by
    calc 16 = 2 ^ 4 := rfl
      _ ≤ 2 ^ k.bits := Nat.pow_le_pow_right (by norm_num) hb4
  have hev : (epTSA e).val = e.val + 8 := epTSA_val' (by omega)
  have hin : InObj e k b := by rw [hbe]; unfold InObj; omega
  rcases hb with (⟨t, ht, K, hK, rfl⟩ | ⟨⟨-, p, k', hp, hk', hin'⟩, hn⟩) | hu
  · have htH : H t = some .tcb := (Heap.drop_eq_some.1 ht).2
    have tf := hH.fits t .tcb htH
    have ta := hH.align t .tcb htH
    simp only [HKind.bits] at tf ta
    have hv : (core.num.U64.wrapping_add t K).val = t.val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hne : t ≠ e := fun h => by subst h; rw [htH] at hek; cases hek; rcases hk with h | h <;> cases h
    have h1 := hin.1; have h2 := hin.2
    have hbv := congrArg UScalar.val hbe
    have t12 : (HKind.tcb).bits = 12 := rfl
    rcases hH.disj t .tcb e k htH hek hne with h | h
    · rw [t12] at h; omega
    · omega
  · obtain ⟨hpD, hpH⟩ := Heap.drop_eq_some.1 hp
    by_cases hpe : p = e
    · subst hpe
      rw [hpH] at hek; cases hek
      rcases hk with rfl | rfl
      · rcases hk' with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
      · rcases hk' with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨-, hw⟩
        · cases h
        · cases h
        · cases h
        · simp only [HKind.bits] at hfit hal
          have hP : p.val % 64 = 0 ∧ p.val + 64 ≤ 2 ^ 64 := ⟨hal, hfit⟩
          rcases hw with e1 | e1 | e1 <;> rw [hbe] at e1 <;> have := congrArg UScalar.val e1 <;>
            simp only [hev, ntfnScA_val hP, ntfnBdA_val hP, ntfnBtA_val hP] at this <;> omega
    · have h1 := hin.1; have h2 := hin.2; have h3 := hin'.1; have h4 := hin'.2
      rcases hH.disj p k' e k hpH hek hpe with h | h <;> omega
  · rcases hu.eps e he with h | h <;> rw [hbe, hev] at h <;> omega

/-- **Writes of cap-slot or untracked words keep `RInv`.** -/
theorem RInv.capwu {s0 s1 s2 : S} (I : RInv st H D Cs s0 s1) (hH : HeapOK H) {B : U64 → Prop}
    (hw : WritesIn st s1 s2 B)
    (hB : ∀ b, B b → CapW (H.drop D).tcbs (H.drop D).omega (H.drop D).frame b ∨
      Untracked st (H.drop D).tcbs Cs (H.drop D) (H.drop D).frame s1 b) : RInv st H D Cs s0 s2 := by
  obtain ⟨Ac1, hb1⟩ := I.blk
  obtain ⟨hb2, pfr, ec, ecs, ea, fld, -, sig⟩ := blk_of_capw_untracked hb1 hw hB
  refine I.step hb2 fld ec ecs ea pfr.idle (fun e he => ?_) sig hw.1 hw.2.1
  obtain ⟨k, hek⟩ : ∃ k, H e = some k := by
    rcases he with he | he <;> exact ⟨_, (Heap.drop_eq_some.1 he).2⟩
  have hfit := hH.fits e k hek
  have hal := hH.align e k hek
  have hb4 : 4 ≤ k.bits := by
    rcases he with he | he <;> rw [(Heap.drop_eq_some.1 he).2] at hek <;> cases hek <;> simp [HKind.bits]
  have h16 : 16 ∣ 2 ^ k.bits := by
    have : 2 ^ k.bits = 2 ^ 4 * 2 ^ (k.bits - 4) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
  have h16' : 16 ≤ 2 ^ k.bits := Nat.le_of_dvd (Nat.two_pow_pos _) h16
  have hev := epTSA_val' (e := e) (by omega)
  have ha : Aligned (epTSA e) := by
    unfold Aligned; rw [hev]; have := Nat.mod_mod_of_dvd e.val h16; omega
  exact hw.mem_eq ha fun hb => ep_not_written hH he (hB _ hb) rfl

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {D : U64 → Prop} {Cs : Set U64}

/-- A word off the preemption point's three. -/
theorem not_ppw {T Ω : Set U64} {H1 : Heap} {X : Set U64} {s1 : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H1 X s1 Q R) {b : U64} (h1 : b.val ≠ (L.ksb s1).val + 40)
    (h2 : b.val ≠ L.nodeBase s1 (L.cpu s1) + 48) (h3 : b.val ≠ L.nodeBase s1 (L.cpu s1) + 40) : ¬ PPW st s1 b := by
  have hN := hq.nodes _ hq.cur
  rintro (e | e | e) <;> have := congrArg UScalar.val e
  · rw [ks_val hq (by simp [layout.ks.WORK_UNITS])] at this; simp [layout.ks.WORK_UNITS] at this; omega
  · unfold LawfulStore.nodeA at this
    rw [nodeAt_val hN (by simp [layout.node.CUR_TIME])] at this; simp [layout.node.CUR_TIME] at this; omega
  · unfold LawfulStore.nodeA at this
    rw [nodeAt_val hN (by simp [layout.node.CONSUMED])] at this; simp [layout.node.CONSUMED] at this; omega

/-- **A preemption point keeps `RInv`.** -/
theorem RInv.pp {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s1 : S} (I : RInv st H D Cs s0 s1)
    (hH : HeapOK H) (a : A) : sched.preemption_point st ar s1 a ⦃ r => RInv st H D Cs s0 r.2.1 ⦄ := by
  obtain ⟨Ac1, hb1⟩ := I.blk
  refine WP.spec_mono (Fl4Proofs.P1.sched.preemption_point.pp (ar := ar) hA s1 a hb1) ?_
  rintro ⟨r, s2, a2⟩ ⟨hb2, w⟩
  simp only at hb2 w ⊢
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, hSg⟩ := hb1
  have hN := hq.nodes _ hq.cur
  have hT := hq.tcbs
  have ks0 : (L.ksb s1).val + 13568 ≤ L.nodeBase s1 (L.cpu s1) := by simp [LawfulStore.nodeBase]
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem s2 (L.nodeA s1 o) = L.mem s1 (L.nodeA s1 o) := fun o ho h8 h48 h40 => by
    refine w.mem_eq (nodeAt_aligned hN ho h8) (not_ppw hq ?_ ?_ ?_) <;>
      unfold LawfulStore.nodeA <;> rw [nodeAt_val hN ho] <;> omega
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem s2 (L.nodeA s2 o) = L.mem s1 (L.nodeA s1 o) := fun o ho h8 h48 h40 => by
    have e : L.nodeA s2 o = L.nodeA s1 o := by unfold LawfulStore.nodeA; rw [w.2.1, nodeAt_of_ksb w.1]
    rw [e]; exact nw o ho h8 h48 h40
  have fld : ∀ y ∈ (H.drop D).tcbs, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K) := by
    intro y hy K hK0 hK hK8
    have hv := field_val (hT y hy) hK
    have hko := hq.ksOut y hy
    have hnd := hN.disj y hy
    refine w.mem_eq (field_aligned (hT y hy) hK hK8) (not_ppw hq ?_ ?_ ?_) <;> rw [hv] <;> omega
  refine I.step hb2 fld ?_ ?_ ?_ ?_ (fun e he => ?_) (fun b hb => ?_) w.1 w.2.1
  · unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)
      (by rw [curth0]; omega)
  · unfold LawfulStore.cscW
    exact nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  · unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
      (by rw [act_val]; omega)
  · unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)
      (by rw [idle8]; omega)
  · obtain ⟨E, EQ, w1, -, -, -, -, -, -, k3, -⟩ := hq.eps
    obtain ⟨hP, ⟨ho1, ho2⟩, -⟩ := w1 e ((k3 e).2 he)
    have hev := epTSA_val hP
    have ho := ho1 _ hq.cur
    have ha : Aligned (epTSA e) := by unfold Aligned; rw [hev]; have := hP.align; omega
    refine w.mem_eq ha (not_ppw hq ?_ ?_ ?_) <;> rw [hev] <;> omega
  · have hks := hSg.ks b hb
    have ho := hq.omega b (hSg.sub b hb)
    have hon := ho.2.2 _ hq.cur
    refine w.mem_eq ho.1 (not_ppw hq ?_ ?_ ?_) <;> omega

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {D : U64 → Prop} {Cs : Set U64}

theorem writesIn_zr' {s : S} {p n : U64} (ha : Aligned p) (hn : n.val % 8 = 0) (hw : p.val + n.val ≤ 2 ^ 64) :
    WritesIn st s (L.zr s p n) (fun b => p.val ≤ b.val ∧ b.val < p.val + n.val) :=
  ⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun b hb hnb => by rw [L.mem_zr _ _ _ _ ha hn hw hb, if_neg hnb]⟩

theorem WritesIn.al {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B) :
    WritesIn st s s' (fun b => Aligned b ∧ B b) :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun h' => hn ⟨hb, h'⟩⟩

/-- **The start of the reset**: the dropped heap's `BlkOK` (`BlkOK.drop`). -/
theorem RInv.start {s : S} {Ac : Set U64} (P : DropOK st H D Cs s)
    (hb : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s) : RInv st H D Cs s s :=
  ⟨⟨Ac, hb.drop P⟩, fun q hq hd => by unfold DeadQ; rw [hq]; exact hd, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- **Clearing part of the region keeps `RInv`.** -/
theorem RInv.clear {lo hi : Nat} {s0 s1 : S} (I : RInv st H (RegionD H lo hi) Cs s0 s1) (hH : HeapOK H)
    (hnode : RegionOffNodes st Cs s0 lo hi) {base n : U64} (ha : Aligned base) (hn : n.val % 8 = 0)
    (hfit : base.val + n.val ≤ 2 ^ 64) (hlo : lo ≤ base.val) (hhi : base.val + n.val ≤ hi) :
    RInv st H (RegionD H lo hi) Cs s0 (L.zr s1 base n) := by
  refine I.capwu hH (writesIn_zr' ha hn hfit).al fun b ⟨hba, h1, h2⟩ => Or.inr ?_
  refine untracked_of_noKept hH hba (noKept_of_region (by omega) (by omega)) fun c hc => ?_
  have e : L.nodeBase s1 c = L.nodeBase s0 c := by simp [LawfulStore.nodeBase, I.ksb]
  rw [e]; rcases hnode.1 c hc with h | h <;> omega

/-- **Rewriting the untyped cap's slot keeps `RInv`.** -/
theorem RInv.setcap {s0 s1 : S} (I : RInv st H D Cs s0 s1) (P : DropOK st H D Cs s0) {x : U64}
    (hxs : CapSlotW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) x)
    (c : capability.Cap) : obj.Slot.set_cap st x s1 c ⦃ s2 => RInv st H D Cs s0 s2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hxa := hxs.1
  have hx := hxs.2
  unfold obj.Slot.set_cap
  refine WP.spec_bind (P0.capability.Cap.encode.p0 c) ?_
  rintro ⟨w0, w1⟩ -
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (LawfulStore.write_spec s1 x w0) fun s2 e2 => ?_
  subst e2
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec _ _ w1) fun s3 e3 => ?_
  subst e3
  have h0 : core.num.U64.wrapping_add x 0#u64 = x := by
    apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  have c0 : CapW H.tcbs H.omega H.frame x := h0 ▸ hx 0#u64 (by simp) (by simp)
  have c8 := hx 8#u64 (by simp) (by simp)
  have a8 : Aligned (core.num.U64.wrapping_add x 8#u64) := by
    unfold Aligned at hxa ⊢; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have I2 := I.capwu P.heap (writesIn_wr (v := w0) hxa) fun b e => by rw [e]; exact capw_drop P I.ksb hxa c0
  have hk2 : L.ksb (L.wr s1 x w0) = L.ksb s0 := by rw [LawfulStore.ksb_wr]; exact I.ksb
  exact I2.capwu P.heap (writesIn_wr (v := w1) a8) fun b e => by rw [e]; exact capw_drop P hk2 a8 c8

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem mask_chunk (v : U64) : (v &&& ~~~65535#u64).val % 65536 = 0 := by
  rw [UScalar.val_and]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_and]
  simp only [Nat.zero_testBit]
  by_cases hi : i < 16
  · have : (~~~65535#u64).val.testBit i = false := by
      have h1 : (~~~65535#u64).val.testBit i = (~~~65535#u64).bv.getLsbD i := rfl
      rw [h1, UScalar.bv_not, BitVec.getLsbD_not]
      have h2 : (65535#u64).bv.getLsbD i = true := by
        have : (65535#u64).bv.getLsbD i = (65535 : Nat).testBit i := by simp [BitVec.getLsbD_ofNat]; omega
        rw [this, show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp [hi]
      rw [h2]; simp
    rw [this]; simp
  · simp [hi]

theorem and63_of_lt {x : U64} (h : x.val < 64) : (x &&& 63#u64).val = x.val := by
  rw [UScalar.val_and, show (63#u64).val = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

theorem shl1_val {x : U64} (h : x.val < 64) :
    (1#u64 <<< (x &&& 63#u64) : Result U64) ⦃ z => z.val = 2 ^ x.val ⦄ := by
  have e := and63_of_lt h
  refine WP.spec_mono (U64.ShiftLeft_spec 1#u64 (x &&& 63#u64) (by rw [e]; simpa using h)) fun z hz => ?_
  rw [hz.1, e]
  simp only [UScalar.val, show (1#u64).bv.toNat = 1 from rfl, Nat.one_shiftLeft, U64.size, U64.numBits]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs : Set U64}

/-- **The chunked reset loop keeps `RInv`**: each chunk `[p + off, p + off + 2^16)`
lies in the region. -/
theorem untyped.reset_untyped_loop.rinv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {p sb : U64} {s0 : S} (P : DropOK st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s0)
    (hnode : RegionOffNodes st Cs s0 p.val (p.val + 2 ^ sb.val)) (hpal : p.val % 2 ^ sb.val = 0)
    (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hsb : 16 ≤ sb.val) {x : U64}
    (hxs : CapSlotW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) x) (dev : Bool) {s1 : S} (a : A) {off : U64}
    (I : RInv st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s0 s1) (h16 : off.val % 65536 = 0)
    (hoff : off.val + 65536 ≤ 2 ^ sb.val) :
    untyped.reset_untyped_loop st ar s1 a x p sb dev off ⦃ r =>
      RInv st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s0 r.2.1 ⦄ := by
  have hdv : 65536 ∣ 2 ^ sb.val := by
    have : 2 ^ sb.val = 2 ^ 16 * 2 ^ (sb.val - 16) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
  have hp16 : p.val % 65536 = 0 := by have := Nat.mod_mod_of_dvd p.val hdv; omega
  unfold untyped.reset_untyped_loop
  apply loop.spec_decr_nat (measure := fun y : S × A × U64 => y.2.2.val)
    (inv := fun y => RInv st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s0 y.1 ∧ y.2.2.val % 65536 = 0 ∧
      y.2.2.val + 65536 ≤ 2 ^ sb.val)
  · rintro ⟨s2, a2, o2⟩ ⟨I2, h2, ho2⟩
    simp only at I2 h2 ho2
    dsimp only
    unfold untyped.reset_untyped_loop.body
    simp only [lift, bind_ok]
    have hv : (core.num.U64.wrapping_add p o2).val = p.val + o2.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine WP.spec_bind (LawfulStore.clear_free_spec s2 _ _) fun s3 e3 => ?_
    subst e3
    have I3 := I2.clear P.heap hnode (base := core.num.U64.wrapping_add p o2) (n := untyped.RESET_CHUNK)
      (by unfold Aligned; rw [hv]; omega) (by simp [untyped.RESET_CHUNK])
      (by rw [hv]; simp [untyped.RESET_CHUNK]; omega) (by rw [hv]; omega)
      (by rw [hv]; simp [untyped.RESET_CHUNK]; omega)
    refine WP.spec_bind (I3.setcap P hxs _) fun s4 I4 => ?_
    split
    · exact (WP.spec_ok _).2 I4
    rename_i hne
    -- #52: the cap just written is read back; a doomed transaction's
    -- `none` ends the loop with `Preempted` (state as written).
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s4 LawfulStore.total) fun c _ => ?_
    refine WP.spec_bind (P0.untyped.as_untyped.p0 c) fun o _ => ?_
    refine p0_if _ _ _ _ (fun _ => (WP.spec_ok _).2 I4) (fun _ => ?_)
    refine WP.spec_bind (I4.pp hA P.heap a2) ?_
    rintro ⟨r, s5, a5⟩ I5
    simp only at I5
    try simp only [uncurry_apply_pair]
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, WP.spec_ok,
        P0.saturating_sub_u64_val]
      have hne' : o2.val ≠ 0 := fun h => hne (UScalar.eq_of_val_eq (by simpa using h))
      have hge : 65536 ≤ o2.val := by omega
      refine ⟨⟨I5, ?_, ?_⟩, ?_⟩ <;> simp [untyped.RESET_CHUNK] <;> omega
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      exact WP.spec_bind (Pₘ := fun _ => True) (WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial)
        fun _ _ => (WP.spec_ok _).2 trivial) fun _ _ => (WP.spec_ok _).2 I5
  · exact ⟨I, h16, hoff⟩

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **`ResetP1Step` holds**: the reset keeps `BlkOK` over the dropped heap,
the dead objects dead and the current thread's words. -/
theorem resetP1Step_holds {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) : ResetP1Step st ar := by
  intro H Cs Ac s a x p sb fi dev hb hcap hxs hpal hfit P hnode hsz
  obtain ⟨hfi, hsb4, hsb64⟩ := hsz
  have I0 := RInv.start P hb
  suffices hR : untyped.reset_untyped st ar s a x ⦃ r =>
      RInv st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s r.2.1 ⦄ by
    refine WP.spec_mono hR fun r I => ?_
    obtain ⟨⟨Ac', hb'⟩, hd, hk, -, -⟩ := I
    exact ⟨_, Ac', hb', fun q => rfl, hd, hk⟩
  have hdv : 8 ∣ 2 ^ sb.val := by
    have : 2 ^ sb.val = 2 ^ 3 * 2 ^ (sb.val - 3) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
  have hp8 : p.val % 8 = 0 := by have := Nat.mod_mod_of_dvd p.val hdv; omega
  unfold untyped.reset_untyped
  rw [hcap]
  simp only [bind_ok, untyped.as_untyped]
  split
  · exact (WP.spec_ok _).2 I0
  split
  · rename_i hd
    simp only [hd, ite_true, bind_ok]
    exact WP.spec_bind (I0.setcap P hxs _) fun s2 I2 => (WP.spec_ok _).2 I2
  rename_i hd
  split
  · simp only [hd, Bool.false_eq_true, ite_false, lift, bind_ok]
    refine WP.spec_bind (Pₘ := fun s1 => RInv st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s s1) ?_
      fun s1 I1 => WP.spec_bind (I1.setcap P hxs _) fun s2 I2 => (WP.spec_ok _).2 I2
    refine WP.spec_bind (shl1_val (x := sb) hsb64) fun n hn => ?_
    refine WP.spec_mono (LawfulStore.clear_free_spec s p n) fun s1 e1 => ?_
    subst e1
    exact I0.clear P.heap hnode (base := p) (n := n) hp8 (by rw [hn]; exact Nat.mod_eq_zero_of_dvd hdv)
      (by rw [hn]; exact hfit) le_rfl (by rw [hn])
  rename_i hfi0 hsmall
  have hsb16 : 16 ≤ sb.val := by
    have : ¬ sb.val < 16 := fun h => hsmall (by simpa [untyped.RESET_CHUNK_BITS] using h)
    omega
  have hfi0' : fi.val ≠ 0 := fun h => hfi0 (UScalar.eq_of_val_eq (by simpa using h))
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  simp only [lift, bind_ok]
  have hm := mask_chunk i
  have h1 : i1 = 65535#u64 := UScalar.eq_of_val_eq (by simp [untyped.RESET_CHUNK] at hi1; simpa using hi1)
  subst h1
  have hle : (i &&& ~~~65535#u64).val ≤ i.val := by rw [UScalar.val_and]; exact Nat.and_le_left
  have hdv16 : 65536 ∣ 2 ^ sb.val := by
    have : 2 ^ sb.val = 2 ^ 16 * 2 ^ (sb.val - 16) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
  have hoff : (i &&& ~~~65535#u64).val + 65536 ≤ 2 ^ sb.val := by
    obtain ⟨k, hk⟩ := hdv16
    have hlt : (i &&& ~~~65535#u64).val < 2 ^ sb.val := by omega
    obtain ⟨j, hj⟩ : 65536 ∣ (i &&& ~~~65535#u64).val := Nat.dvd_of_mod_eq_zero hm
    rw [hk] at hlt ⊢; rw [hj] at hlt ⊢
    have : j < k := by omega
    omega
  exact untyped.reset_untyped_loop.rinv hA P hnode hpal hfit hsb16 hxs dev a I0 hm hoff

end

end Fl4Proofs.P1
