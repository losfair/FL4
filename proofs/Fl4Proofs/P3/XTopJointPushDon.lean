/-
P3 (DESIGN.md §9), IPC: **the donating `reply_push` at `J`** (toward
XTopJointSendPush's `JSendRecvHyp`): a call to a receiver with a reply object
and no SC, with `can_donate`: after the link and the caller's block (a `J`
state, XTopJointSendPushD), FL4 pushes the reply on the caller's SC's call
stack and donates the SC to the receiver; l4v `reply_push` with
`bind_sc_reply` and `sched_context_donate`.

* `ipc.push_don.blk` (P1): the stack writes and the donation keep `BlkOK`
  (as `ipc.reply_push.ipc`'s donating branch, from `BlkOK` at the block),
  inside `KW` (the receiver on the SC's core: `donate.kwAX`).
* `Sched.push_donate_refinesW`: ScCallPushRef's `push_donate_refines` with
  the call stacks after named (`Function.update Lst sc (r :: Lst sc)`) and the
  links of the replies other than `r` and the old head kept.
* The spec's state after (`bdSt`: `bind_sc_reply`; `pdSt`: then the
  donation of the current thread's SC, `dnSt`), `bindScReply_eq`,
  `donate_curN_eq`, `pd_eq`, and what `bdSt` keeps (`bd_*`).
* **`JAtZ.pushDonJ`**: the donation part of `reply_push` from `JAtZ` to
  `JAtZ` (XTopJointFinScReply's `JAtZ.sc_frameS` with the frame words of
  XTopJointRemove's `RmW`).
-/
import Fl4Proofs.P3.XTopJointSendPush
import Fl4Proofs.P3.XTopJointRemove
import Fl4Proofs.P3.XTopJointStsI
open Aeneas Aeneas.Std Result

/-! ## P1: the stack writes and the donation -/

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat} {Es : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The donating part of `reply_push` keeps `BlkOK`**, inside `KW`
(module docstring): from `BlkOK` with the caller blocked (its SC `i`), the
callee without an SC on `i`'s core, both in no queue. -/
theorem ipc.push_don.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (caller callee r i : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hcl : caller ∈ T) (hcq : (L.mem s (inqA caller) &&& sched.Q_QUEUED) = 0#u64)
    (hcr : (L.mem s (inqA caller) &&& sched.Q_RELEASE) = 0#u64) (hca : L.actionW s ≠ caller)
    (hci : L.idleW s ≠ caller) (hr : r ∈ Rp) (hce : callee ∈ T) (hne : callee ≠ caller)
    (heq : (L.mem s (inqA callee) &&& sched.Q_QUEUED) = 0#u64)
    (her : (L.mem s (inqA callee) &&& sched.Q_RELEASE) = 0#u64) (hea : L.actionW s ≠ callee)
    (hcei : L.idleW s ≠ callee)
    (hi : L.mem s (scA caller) = i) (hi0 : i ≠ 0#u64) (hiA : i ∈ Ac) (hd0 : L.mem s (scA callee) = 0#u64)
    (haff : L.mem s (affA callee) = L.mem s (scCoreA i)) :
    (do
      let i2 ← obj.Sc.reply st i s
      let s3 ← if i2 != 0#u64 then obj.Reply.set_next st i2 s r false else ok s
      let s4 ← obj.Reply.set_prev st r s3 i2
      let s5 ← obj.Sc.set_reply st i s4 r
      let s6 ← obj.Reply.set_next st r s5 i true
      schedcontext.donate st ar s6 a i callee) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
        Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  obtain ⟨hiS, -, -⟩ := hX.2.2.bound caller hcl (by rw [hi]; exact hi0)
  rw [hi] at hiS
  have hcO : scCoreA i ∈ Ω := (hcΩ i hiS).2.1
  have hiv := sc_facts hO hiS
  have hi8 := (sc_lo (hO.sc i hiS).1 (hO.sc i hiS).2).1
  step with obj.Sc.reply.val as ⟨i2, ei2⟩
  have hi2 : i2 ≠ 0#u64 → i2 ∈ Rp := fun h0 => by rw [ei2] at h0 ⊢; exact hX.2.1.screp i hiS h0
  -- the four stack writes
  have pre : ∀ (s3 : S), SchedQueuesInv st T Cs Ω H s3 Q R → BoundInv st T Ac s3 → XInv st T Cs Ω Sg Rp Scs Nt Z s3 →
      SCsOK st T Ω Sg Scs Z Ac s3 → SgOK st Ω Sg s3 →
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) →
      (L.actionW s3 = L.actionW s) → L.idleW s3 = L.idleW s →
      L.mem s3 (scReplyA i) = i2 → (i2 ≠ 0#u64 → headBit (L.mem s3 (rNextA i2)) = false) →
      L.mem s3 (scCoreA i) = L.mem s (scCoreA i) → Foot st T Cs Sg Scs Z Es s s3 →
      (do
        let s4 ← obj.Reply.set_prev st r s3 i2
        let s5 ← obj.Sc.set_reply st i s4 r
        let s6 ← obj.Reply.set_next st r s5 i true
        schedcontext.donate st ar s6 a i callee) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          Foot st T Cs Sg Scs Z Es s s' ⦄ := by
    intro s3 h3 hB3 hX3 hS3 hSg3 f3 a3 i3 hr3 hn3 c3 F3
    obtain ⟨r32, rt0, rp8, rn16⟩ := rp_facts hO hr
    have ri : ∀ c ∈ Scs, r.val + 32 ≤ c.val ∨ c.val + 2 ^ Z c ≤ r.val := hO.rpSc r hr
    have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
    -- `r.prev := i2`
    step with obj.Reply.set_prev.val as ⟨s4, e4⟩
    obtain ⟨h4, hB4, hX4, hS4, hSg4, a4, -, i4, f4, o4⟩ := link_all (w := i2 &&& ~~~1#u64) h3 hB3 hX3 hS3 hSg3
      ((hrΩ r hr).2.1)
      (fun r' hr' e => by rw [rp8, rTcbA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
      (rword_ne_sc hO hr (by rw [rp8]; omega))
      (fun r' hr' e => by rw [rp8, rNextA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
      (fun r' hr' _ hne => by
        by_cases h0 : i2 = 0#u64
        · subst h0; exact absurd (by rw [zero_or_masked, zero_or_masked]) hne
        · have hp := hi2 h0
          have hev : i2.val % 2 = 0 := by have := rr i2 hp; omega
          rw [mask1_of_even (x := i2) hev, mask1_of_even (x := i2) hev]
          exact hp)
      (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [rp8]; omega) c hc))
      (fun n hn e => by rw [rp8] at e; have := hO.ntRp n hn r hr; omega)
      (fun n hn e => by rw [rp8, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn r hr; omega)
      (rword_ne_scn hO hr (by rw [rp8]; omega)) (rword_ne_scy hO hr (by rw [rp8]; omega))
      (rword_ne_spor hO hr (by rw [rp8]; omega))
      (fun r' hr' e => by rw [rp8, rNextA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
      (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [rp8]; omega) c hc))
    rw [← e4] at h4 hB4 hX4 hS4 hSg4 a4 i4 f4 o4
    have tci4 : L.mem s4 (scTcbA i) = caller := by
      have e : L.mem s4 (scA caller) = i := by
        rw [scA_eq, f4 caller hcl _ (by simp) (by simp), f3 caller hcl _ (by simp) (by simp), ← scA_eq, hi]
      have := (hX4.2.2.bound caller hcl (by rw [e]; exact hi0)).2.1
      rw [e] at this; exact this
    have id4 : L.idleW s4 = L.idleW s := i4.trans i3
    have hr4 : L.mem s4 (scReplyA i) = i2 := by
      rw [o4 _ (hsub _ (hO.repW i hiS)) (rword_ne_screp hO hr (by rw [rp8]; omega) i hiS)]; exact hr3
    have hn4 : i2 ≠ 0#u64 → headBit (L.mem s4 (rNextA i2)) = false := fun h0 => by
      rw [o4 _ (hrΩ i2 (hi2 h0)).2.2 (by rw [rp8, rNextA_val (hO.rp i2 (hi2 h0))]; have := rr i2 (hi2 h0); omega)]
      exact hn3 h0
    have c4 : L.mem s4 (scCoreA i) = L.mem s (scCoreA i) :=
      (o4 _ hcO (rword_ne_sc hO hr (by rw [rp8]; omega) i hiS).2.1).trans c3
    have F4 : Foot st T Cs Sg Scs Z Es s s4 :=
      F3.trans (by rw [e4]; exact foot_wr (h3.omega _ (hrΩ r hr).2.1).1 (kw_sg (hO.prevW hr)))
    -- `sc.reply := r`
    step with obj.Sc.set_reply.spec as ⟨s5, e5⟩
    have hiR : ∀ c ∈ Scs, c ≠ i → i.val + 2 ^ Z i ≤ c.val ∨ c.val + 2 ^ Z c ≤ i.val := fun c hc hne =>
      hO.scDisj i hiS c hc (Ne.symm hne)
    obtain ⟨h5, hB5, hX5, hS5, hSg5, a5, -, i5, f5, o5⟩ := link_all (w := r) h4 hB4 hX4 hS4 hSg4
      (hsub _ (hO.repW i hiS))
      (fun r' hr' e => by
        rw [hiv.2.2.2.2.2.2.1, rTcbA_val (hO.rp r' hr')] at e
        have := hO.rpSc r' hr' i hiS; have := hiv.1; omega)
      (fun c hc => by
        obtain ⟨h128c, e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc
        rw [hiv.2.2.2.2.2.2.1, e1, e2, e3, e4, e5]
        have := hiv.1
        by_cases hci : c = i
        · subst hci; omega
        · have := hiR c hc hci; omega)
      (fun r' hr' e => by
        rw [hiv.2.2.2.2.2.2.1, rNextA_val (hO.rp r' hr')] at e
        have := hO.rpSc r' hr' i hiS; have := hiv.1; omega)
      (fun r' hr' e => by
        rw [hiv.2.2.2.2.2.2.1, rPrevA_val (hO.rp r' hr')] at e
        have := hO.rpSc r' hr' i hiS; have := hiv.1; omega)
      (fun c hc e _ => by
        by_cases hci' : c = i
        · rw [hci', tci4, id4]; exact ⟨hr, hiA, fun e' => hci e'.symm⟩
        · exfalso; have := hiR c hc hci'
          rw [hiv.2.2.2.2.2.2.1, (sc_facts hO hc).2.2.2.2.2.2.1] at e
          have := hiv.1; have := (sc_facts hO hc).1; omega)
      (fun n hn e => by rw [hiv.2.2.2.2.2.2.1] at e; have := hO.ntSc n hn i hiS; have := hiv.1; omega)
      (fun n hn e => by
        rw [hiv.2.2.2.2.2.2.1, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntOSc n hn i hiS; have := hiv.1; omega)
      (fun c hc e => by
        obtain ⟨hPc, hzc⟩ := hO.sc c hc
        rw [hiv.2.2.2.2.2.2.1, scNtfnA_val hPc hzc] at e
        have := hiv.1; have := (sc_facts hO hc).1
        by_cases hci : c = i
        · subst hci; omega
        · have := hiR c hc hci; omega)
      (fun c hc e => by
        rw [hiv.2.2.2.2.2.2.1, show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl,
          (sc_facts hO hc).2.2.2.2.2.2.2] at e
        have := hiv.1; have := (sc_facts hO hc).1
        by_cases hci : c = i
        · subst hci; omega
        · have := hiR c hc hci; omega)
      (scw_ne_spor hO hiS hiv.2.2.2.2.2.2.1 (by omega) (by omega))
      (fun r' hr' e => by
        rw [hiv.2.2.2.2.2.2.1, rNextA_val (hO.rp r' hr')] at e
        have := hO.rpSc r' hr' i hiS; have := hiv.1; omega)
      (fun c hc e r' hr' hb h0 ec => by
        exfalso
        have hci : c = i := by
          by_contra hci
          have := hiR c hc hci
          rw [hiv.2.2.2.2.2.2.1, (sc_facts hO hc).2.2.2.2.2.2.1] at e
          have := hiv.1; have := (sc_facts hO hc).1; omega
        subst hci
        have hh := hX4.2.1.head r' hr' hb h0
        rw [ec, hr4] at hh
        by_cases hz : i2 = 0#u64
        · exact hO.rp0 r' hr' (hh.symm.trans hz)
        · have := hn4 hz; rw [hh] at this; rw [this] at hb; exact absurd hb (by decide))
    rw [← e5] at h5 hB5 hX5 hS5 hSg5 a5 i5 f5 o5
    have c5 : L.mem s5 (scCoreA i) = L.mem s (scCoreA i) :=
      (o5 _ hcO (by rw [hiv.2.2.2.2.2.2.1, hiv.2.2.1]; omega)).trans c4
    have F5 : Foot st T Cs Sg Scs Z Es s s5 :=
      F4.trans (by rw [e5]; exact foot_wr (h4.omega _ (hsub _ (hO.repW i hiS))).1 (kw_sg (hO.repW i hiS)))
    -- `r.next := i` (head)
    step with obj.Reply.set_next.val1 as ⟨s6, e6⟩
    have hi_ev : i &&& ~~~1#u64 = i := mask1_of_even (by omega)
    obtain ⟨h6, hB6, hX6, hS6, hSg6, a6, -, i6, f6, o6⟩ := link_all (w := (i &&& ~~~1#u64) ||| 1#u64)
      h5 hB5 hX5 hS5 hSg5 ((hrΩ r hr).2.2)
      (fun r' hr' e => by rw [rn16, rTcbA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
      (rword_ne_sc hO hr (by rw [rn16]; omega))
      (fun r' hr' _ _ => by
        refine ⟨fun _ => ?_, fun hb0 => absurd hb0 (by rw [nx_head1]; simp)⟩
        rw [nx_mask _ _ (Or.inr rfl), hi_ev]; exact hiS)
      (fun r' hr' e => by rw [rn16, rPrevA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
      (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [rn16]; omega) c hc))
      (fun n hn e => by rw [rn16] at e; have := hO.ntRp n hn r hr; omega)
      (fun n hn e => by rw [rn16, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn r hr; omega)
      (rword_ne_scn hO hr (by rw [rn16]; omega)) (rword_ne_scy hO hr (by rw [rn16]; omega))
      (rword_ne_spor hO hr (by rw [rn16]; omega))
      (fun r' hr' e _ _ => by
        have : r' = r := UScalar.eq_of_val_eq (by
          rw [rn16, rNextA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
        subst this
        rw [nx_mask _ _ (Or.inr rfl), hi_ev, e5]
        exact L.mem_wr_same (h4.omega _ (hsub _ (hO.repW i hiS))).1)
      (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [rn16]; omega) c hc))
    rw [← e6] at h6 hB6 hX6 hS6 hSg6 a6 i6 f6 o6
    have c6 : L.mem s6 (scCoreA i) = L.mem s (scCoreA i) :=
      (o6 _ hcO (rword_ne_sc hO hr (by rw [rn16]; omega) i hiS).2.1).trans c5
    have F6 : Foot st T Cs Sg Scs Z Es s s6 :=
      F5.trans (by rw [e6]; exact foot_wr (h5.omega _ (hrΩ r hr).2.2).1 (kw_sg (hO.nextW hr)))
    -- the donation
    have F : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → L.mem s6 (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
      ((f6 y hy K hK hK8).trans ((f5 y hy K hK hK8).trans (f4 y hy K hK hK8))).trans (f3 y hy K hK hK8)
    have ea6 : L.actionW s6 = L.actionW s := (a6.trans (a5.trans a4)).trans a3
    have ei6 : L.idleW s6 = L.idleW s := (i6.trans (i5.trans i4)).trans i3
    have sc6 : ∀ y ∈ T, L.mem s6 (scA y) = L.mem s (scA y) := fun y hy => by
      rw [scA_eq, F y hy _ (by simp) (by simp), ← scA_eq]
    have iq6 : ∀ y ∈ T, L.mem s6 (inqA y) = L.mem s (inqA y) := fun y hy => by
      rw [inqA_eq, F y hy _ (by simp) (by simp), ← inqA_eq]
    have tci6 : L.mem s6 (scTcbA i) = caller := by
      have e : L.mem s6 (scA caller) = i := by rw [sc6 caller hcl, hi]
      have := (hX6.2.2.bound caller hcl (by rw [e]; exact hi0)).2.1
      rw [e] at this; exact this
    have haff6 : L.mem s6 (affA callee) = L.mem s6 (scCoreA i) := by
      rw [affA_eq, F callee hce _ (by simp) (by simp), ← affA_eq, c6]; exact haff
    refine WP.spec_mono (WP.spec_and
      (schedcontext.donate.ipc hA s6 a i callee caller Q R h6 hB6 hX6 hS6 hSg6 hcl (by rw [sc6 caller hcl, hi]) hi0
        ⟨by rw [iq6 caller hcl]; exact hcq, by rw [iq6 caller hcl]; exact hcr, by rw [ea6]; exact hca⟩
        (by rw [ei6]; exact hci) hce (by rw [sc6 callee hce]; exact hd0) (by rw [iq6 callee hce]; exact heq)
        (by rw [iq6 callee hce]; exact her) (by rw [ea6]; exact hea) hne hiA (by rw [ei6]; exact hcei))
      (schedcontext.donate.kwAX (Es := Es) hA s6 a i callee caller h6 hB6 hX6 hS6 hSg6 hiS hce hcl tci6
        ⟨by rw [iq6 caller hcl]; exact hcq, by rw [iq6 caller hcl]; exact hcr⟩)) fun r' hh => ?_
    obtain ⟨s', a'⟩ := r'
    simp only [WP.uncurry'_pair] at hh ⊢
    exact ⟨hh.1.1, F6.trans (hh.2 haff6)⟩
  split
  · rename_i hne0
    have h0 : i2 ≠ 0#u64 := by simpa using hne0
    have hp2 := hi2 h0
    obtain ⟨p32, pt0, pp8, pn16⟩ := rp_facts hO hp2
    have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
    step with obj.Reply.set_next.val0 as ⟨s3, e3⟩
    obtain ⟨h3, hB3, hX3, hS3, hSg3, a3, -, i3, f3, o3⟩ := link_all (w := (r &&& ~~~1#u64) ||| 0#u64)
      h hB hX hS hSg ((hrΩ i2 hp2).2.2)
      (fun r' hr' e => by rw [pn16, rTcbA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
      (rword_ne_sc hO hp2 (by rw [pn16]; omega))
      (fun r' hr' _ _ => by
        refine ⟨fun hb1 => absurd hb1 (by rw [nx_head0]; simp), fun _ => ?_⟩
        rw [nx_mask _ _ (Or.inl rfl), mask1_of_even (x := r) (by have := rr r hr; omega)]; exact hr)
      (fun r' hr' e => by rw [pn16, rPrevA_val (hO.rp r' hr')] at e; have := rr r' hr'; omega)
      (fun c hc e => absurd e (rword_ne_screp hO hp2 (by rw [pn16]; omega) c hc))
      (fun n hn e => by rw [pn16] at e; have := hO.ntRp n hn i2 hp2; omega)
      (fun n hn e => by rw [pn16, ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn i2 hp2; omega)
      (rword_ne_scn hO hp2 (by rw [pn16]; omega)) (rword_ne_scy hO hp2 (by rw [pn16]; omega))
      (rword_ne_spor hO hp2 (by rw [pn16]; omega))
      (fun r' hr' _ hb1 => absurd hb1 (by rw [nx_head0]; simp))
      (fun c hc e => absurd e (rword_ne_screp hO hp2 (by rw [pn16]; omega) c hc))
    rw [← e3] at h3 hB3 hX3 hS3 hSg3 a3 i3 f3 o3
    refine pre s3 h3 hB3 hX3 hS3 hSg3 f3 a3 i3 ?_ (fun _ => ?_) ?_ ?_
    · rw [e3, L.mem_wr_ne (h.omega _ (hrΩ i2 hp2).2.2).1 (h.omega _ (hsub _ (hO.repW i hiS))).1
        (rword_ne_screp hO hp2 (by rw [pn16]; omega) i hiS)]; exact ei2.symm
    · rw [e3, L.mem_wr_same (h.omega _ (hrΩ i2 hp2).2.2).1]; exact nx_head0 _
    · exact o3 _ hcO (rword_ne_sc hO hp2 (by rw [pn16]; omega) i hiS).2.1
    · rw [e3]; exact foot_wr (h.omega _ (hrΩ i2 hp2).2.2).1 (kw_sg (hO.nextW hp2))
  · try simp only [Aeneas.Std.bind_ok]
    rename_i hz
    have hz' : i2 = 0#u64 := UScalar.eq_of_val_eq (by simpa using hz)
    exact pre s h hB hX hS hSg (fun _ _ _ _ _ => rfl) rfl rfl ei2.symm (fun h0 => absurd hz' h0) rfl (Foot.refl _)

end

end Fl4Proofs.P1

/-! ## The donating push on the scheduler relation, the call stacks named -/

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **`reply_push`'s donation branch refines `bind_sc_reply` and
`sched_context_donate`**: the caller `f`'s SC `sc` takes the detached,
isolated reply `r` on its stack and moves to the callee `t` (which has no
SC). -/
theorem push_donate_refinesW {N T C R : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) {f : U64} (hf : f ∈ T) (hyf : y.scTcb = some f.bv)
    {xf : Fl4Spec.Tcb} (hkf : σ.kheap f.bv = some (.tcb xf)) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t.bv = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none) (hft : f ≠ t)
    (hrel : inClassR xt.tcbState xt.tcbFault → Fl4Spec.scActive y = true → released σ y)
    {r : U64} (hr : r ∈ R) (hdet : Detached C Lst r) (hiso : Isolated (L.mem s) R r)
    (hRF : RFree (L.mem s) R C σ Lst) (hnf : ¬ Free σ r) :
    (do
      let i2 ← obj.Sc.reply st sc s
      let s3 ← if i2 != 0#u64 then obj.Reply.set_next st i2 s r false else ok s
      let s4 ← obj.Reply.set_prev st r s3 i2
      let s5 ← obj.Sc.set_reply st sc s4 r
      let s6 ← obj.Reply.set_next st r s5 sc true
      schedcontext.donate st ar s6 a sc t) ⦃ res => res.2 = a ∧ ∃ σ',
      (do
        Fl4Spec.bindScReply (Z := Unit) sc.bv r.bv
        Fl4Spec.schedContextDonate (Z := Unit) sc.bv t.bv) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c res.1 σ' ∧ NtfnStateRel N T (L.mem res.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      CallRel (L.mem res.1) R C σ' (Function.update Lst sc (r :: Lst sc)) ∧ RPlaced st N T C R c res.1 σ' ∧
      RFree (L.mem res.1) R C σ' (Function.update Lst sc (r :: Lst sc)) ∧
      WritesIn st s res.1 (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) ∧
      (∀ d ∈ R, d ≠ r → (Lst sc).head? ≠ some d →
        L.mem res.1 (rNextA d) = L.mem s (rNextA d) ∧ L.mem res.1 (rPrevA d) = L.mem s (rPrevA d)) ⦄ := by
  have hP := hS.placed
  obtain ⟨⟨y0, n0, hk0, hyL⟩, hLR, hLnd, hLw⟩ := hCR.stack sc hsc
  rw [hk] at hk0; cases hk0
  obtain ⟨haP, hvP, hszP⟩ := sc_reply_word hS hsc
  have hA := hRP.align r hr
  obtain ⟨xr, hkr, hxr⟩ := hCR.reply r hr
  have hpr : sc.bv ≠ r.bv := fun e => by rw [e, hkr] at hk; cases hk
  have hal : ∀ d ∈ R, Aligned (rPrevA d) ∧ Aligned (rNextA d) := fun d hd =>
    ⟨hRP.aligned hd (Or.inl (rPrevA_val (hRP.align d hd))), hRP.aligned hd (Or.inr (rNextA_val (hRP.align d hd)))⟩
  have hfarS : ∀ q ∈ C, ∀ d ∈ R, (scReplyA q).val ≠ (rPrevA d).val ∧ (scReplyA q).val ≠ (rNextA d).val := by
    intro q hq d hd
    obtain ⟨-, hvq, hszq⟩ := sc_reply_word hS hq
    obtain ⟨Q, R', hc, hs⟩ := hS.lists
    obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
    have := hRP.sc d hd q hq xq nq hkq; have := hszq xq nq hkq
    rw [hvq, rPrevA_val (hRP.align d hd), rNextA_val (hRP.align d hd)]; omega
  have hSne : ∀ q ∈ C, q ≠ sc → (scReplyA q).val ≠ (scReplyA sc).val := by
    intro q hq e
    obtain ⟨-, hvq, -⟩ := sc_reply_word hS hq
    rw [hvq, hvP]; exact fun h => e (UScalar.eq_of_val_eq (by omega))
  have hsc2 : sc.val % 2 = 0 := by
    obtain ⟨Q, R', hc, hs⟩ := hS.lists
    obtain ⟨x, n', -, hx⟩ := hs.scs sc hsc
    have := hx.bounds.1; omega
  have hev : ∀ d ∈ R, d.val % 2 = 0 := fun d hd => by have := (hRP.align d hd).1; omega
  have hwr : ∀ {s0 : S} {a b v : U64}, Aligned a → Aligned b → a.val ≠ b.val → L.mem (L.wr s0 a v) b = L.mem s0 b :=
    fun ha hb h => L.mem_wr_ne ha hb h
  have hrL : r ∉ Lst sc := hdet sc hsc
  have hhR : ∀ d, (Lst sc).head? = some d → d ∈ R := fun d h => hLR d (List.mem_of_mem_head? h)
  have hhr : ∀ d, (Lst sc).head? = some d → d ≠ r := fun d h e => hrL (e ▸ List.mem_of_mem_head? h)
  have hi2e : ((Lst sc).headD 0#u64).val % 2 = 0 := by
    cases hL : Lst sc with
    | nil => rfl
    | cons d l => exact hev d (hLR d (by rw [hL]; simp))
  have hpf : sc.bv ≠ f.bv := fun e => by rw [e, hkf] at hk; cases hk
  have hpt : sc.bv ≠ t.bv := fun e => by rw [e, hkt] at hk; cases hk
  have hrf : r.bv ≠ f.bv := fun e => by rw [e, hkf] at hkr; cases hkr
  have hrt : r.bv ≠ t.bv := fun e => by rw [e, hkt] at hkr; cases hkr
  have cwr : ∀ {s0 : S} {a : U64} {v : U64}, Aligned a → CallW' R C a →
      WritesIn st s0 (L.wr s0 a v) (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) :=
    fun ha hc => (writesIn_wr ha).mono fun b hb => hb ▸ Or.inr hc
  have tr : ∀ {x y z : S}, WritesIn st x y (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) →
      WritesIn st y z (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) →
      WritesIn st x z (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) :=
    fun h1 h2 => (h1.trans h2).mono fun b hb => hb.elim id id
  -- the part after the old head's `NEXT` word
  have cont : ∀ (s3 : S) (σA : Fl4Spec.State Unit),
      SchedRel st N T C c s3 σA → NtfnStateRel N T (L.mem s3) σA → NSC N C σA → Inv σA →
      L.ksb s3 = L.ksb s →
      (∀ q, (∀ d, (Lst sc).head? = some d → q ≠ d.bv) → σA.kheap q = σ.kheap q) →
      (∀ d x, (Lst sc).head? = some d → σ.kheap d.bv = some (.reply x) →
        σA.kheap d.bv = some (.reply { x with replySc := none })) →
      σA.curTime = σ.curTime →
      ((Lst sc = [] ∧ σA = σ) ∨ (∃ d l x, Lst sc = d :: l ∧ σ.kheap d.bv = some (.reply x) ∧
        σA = updK σ d.bv (.reply { x with replySc := none }))) →
      (∀ b, Aligned b → (∀ d, (Lst sc).head? = some d → b.val ≠ (rNextA d).val) → L.mem s3 b = L.mem s b) →
      (∀ d, (Lst sc).head? = some d → L.mem s3 (rNextA d) = r) →
      WritesIn st s s3 (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) →
      (do
        let s4 ← obj.Reply.set_prev st r s3 ((Lst sc).headD 0#u64)
        let s5 ← obj.Sc.set_reply st sc s4 r
        let s6 ← obj.Reply.set_next st r s5 sc true
        schedcontext.donate st ar s6 a sc t) ⦃ res => res.2 = a ∧ ∃ σ',
        (do
          Fl4Spec.bindScReply (Z := Unit) sc.bv r.bv
          Fl4Spec.schedContextDonate (Z := Unit) sc.bv t.bv) σ = ({((), σ')}, False) ∧
        SchedRel st N T C c res.1 σ' ∧ NtfnStateRel N T (L.mem res.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        CallRel (L.mem res.1) R C σ' (Function.update Lst sc (r :: Lst sc)) ∧ RPlaced st N T C R c res.1 σ' ∧
        RFree (L.mem res.1) R C σ' (Function.update Lst sc (r :: Lst sc)) ∧
      WritesIn st s res.1 (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) ∧
      (∀ d ∈ R, d ≠ r → (Lst sc).head? ≠ some d →
        L.mem res.1 (rNextA d) = L.mem s (rNextA d) ∧ L.mem res.1 (rPrevA d) = L.mem s (rPrevA d)) ⦄ := by
    intro s3 σA hS3 hR3 hN3 hI3 hks3 hkA hkh3 htm3 hcase hm3 hmH3 hw3
    have hPr := (hal r hr).1
    have hNr := (hal r hr).2
    have hnh_sc : ∀ d, (Lst sc).head? = some d → sc.bv ≠ d.bv := fun d h e => by
      obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d h); rw [← e, hk] at hkd; cases hkd
    have hnh_r : ∀ d, (Lst sc).head? = some d → r.bv ≠ d.bv := fun d h e => hhr d h (eq_of_bv e).symm
    have hk3 : σA.kheap sc.bv = some (.schedContext y n) := by rw [hkA _ hnh_sc]; exact hk
    have hkr3 : σA.kheap r.bv = some (.reply xr) := by rw [hkA _ hnh_r]; exact hkr
    have hSzA : SzKeep σ σA := by
      intro q x' n' hq
      by_cases hq' : ∃ d, (Lst sc).head? = some d ∧ q = d.bv
      · obtain ⟨d, hh, rfl⟩ := hq'
        obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d hh)
        rw [hkh3 d xd hh hkd] at hq; cases hq
      · rw [hkA q (fun d hh e => hq' ⟨d, hh, e⟩)] at hq; exact ⟨x', hq⟩
    have hRP3 : RPlaced st N T C R c s3 σA := hRP.frame hks3 hSzA
    -- `PREV` of `r`
    refine WP.spec_bind (obj.Reply.set_prev.val s3 r _) ?_
    rintro s4 rfl
    rw [and_not1 _ hi2e]
    have hS4 := hS3.wr_far hPr (hRP3.far hr (Or.inl (rPrevA_val hA))) ((Lst sc).headD 0#u64)
    have hR4 : NtfnStateRel N T (L.mem (L.wr s3 (rPrevA r) ((Lst sc).headD 0#u64))) σA :=
      hR3.frame hP (footEq_wr_far hP hPr (fun n hn => by have := hRP.ntfn r hr n hn; rw [rPrevA_val hA]; omega)
        (fun t ht => by have := hRP.tcb r hr t ht; rw [rPrevA_val hA]; omega) _) (KView.refl _)
    -- `REPLY` of `sc`
    refine WP.spec_bind (obj.Sc.set_reply.spec _ sc r) ?_
    rintro s5 rfl
    obtain ⟨hS5, hf5, hK6, -⟩ := hS4.set_sc_reply hsc hk3 r (r.bv :: y.scReplies)
    set σB1 := updSc σA sc.bv { y with scReplies := r.bv :: y.scReplies } n with hσB1
    have hR5 := hR4.frame hS4.placed hf5 hK6
    have hkB1 : ∀ q, q ≠ sc.bv → σB1.kheap q = σA.kheap q := fun q hq => by simp [σB1, updK, hq]
    have hk3B1 : σB1.kheap sc.bv = some (.schedContext { y with scReplies := r.bv :: y.scReplies } n) := by
      simp [σB1, updK]
    have hSz1 : SzKeep σA σB1 := by
      intro q x' n' hq
      by_cases e : q = sc.bv
      · subst e; rw [hk3B1] at hq; cases hq; exact ⟨y, hk3⟩
      · rw [hkB1 q e] at hq; exact ⟨x', hq⟩
    have hRP5 : RPlaced st N T C R c (L.wr (L.wr s3 (rPrevA r) ((Lst sc).headD 0#u64)) (scReplyA sc) r) σB1 :=
      hRP3.frame (by simp) hSz1
    -- `NEXT` of `r`
    refine WP.spec_bind (obj.Reply.set_next.val1 _ r sc) ?_
    rintro s6 rfl
    rw [and_not1 _ hsc2]
    have hS6' := hS5.wr_far hNr (hRP5.far hr (Or.inr (rNextA_val hA))) (sc ||| 1#u64)
    have hkrB1 : σB1.kheap r.bv = some (.reply xr) := by rw [hkB1 _ (Ne.symm hpr)]; exact hkr3
    set σB := updK σB1 r.bv (.reply { xr with replySc := some sc.bv }) with hσB
    have hS6 := hS6'.stableW (WritesIn.refl _ _) (NtfnStepW.updReply hkrB1 { xr with replySc := some sc.bv })
    have hR6 : NtfnStateRel N T (L.mem (L.wr (L.wr (L.wr s3 (rPrevA r) ((Lst sc).headD 0#u64)) (scReplyA sc) r)
        (rNextA r) (sc ||| 1#u64))) σB :=
      hR5.frame hP (footEq_wr_far hP hNr (fun n hn => by have := hRP.ntfn r hr n hn; rw [rNextA_val hA]; omega)
        (fun t ht => by have := hRP.tcb r hr t ht; rw [rNextA_val hA]; omega) _) (KView.updReply hkrB1 _)
    have hkB : ∀ q, q ≠ r.bv → σB.kheap q = σB1.kheap q := fun q hq => by simp [σB, updK, hq]
    have hkscB : σB.kheap sc.bv = some (.schedContext { y with scReplies := r.bv :: y.scReplies } n) := by
      rw [hkB _ hpr]; exact hk3B1
    have hkrB : σB.kheap r.bv = some (.reply { xr with replySc := some sc.bv }) := by simp [σB, updK]
    have hIB : Inv σB :=
      (hI3.scFields (y' := { y with scReplies := r.bv :: y.scReplies }) hk3 rfl rfl rfl rfl).updReply hkrB1
    have hNB : NSC N C σB := (hN3.updSc).updReply hkrB1 _
    have hSzB : SzKeep σ σB := by
      intro q x' n' hq
      by_cases e : q = r.bv
      · subst e; rw [hkrB] at hq; cases hq
      · rw [hkB q e] at hq
        obtain ⟨x0, hx0⟩ := hSz1 q x' n' hq
        exact hSzA q x0 n' hx0
    have hRP6 := hRP.frame (s' := L.wr (L.wr (L.wr s3 (rPrevA r) ((Lst sc).headD 0#u64)) (scReplyA sc) r)
      (rNextA r) (sc ||| 1#u64)) (by simp [hks3]) hSzB
    -- the call stack
    set s6 := L.wr (L.wr (L.wr s3 (rPrevA r) ((Lst sc).headD 0#u64)) (scReplyA sc) r) (rNextA r) (sc ||| 1#u64)
      with hs6
    have hm6 : ∀ b, Aligned b → b.val ≠ (rPrevA r).val → b.val ≠ (scReplyA sc).val → b.val ≠ (rNextA r).val →
        L.mem s6 b = L.mem s3 b := fun b hb h1 h2 h3 => by
      rw [hs6, hwr hNr hb (Ne.symm h3), hwr haP hb (Ne.symm h2), hwr hPr hb (Ne.symm h1)]
    have hP6 : ∀ d ∈ R, d ≠ r → L.mem s6 (rPrevA d) = L.mem s (rPrevA d) := by
      intro d hd hdr
      rw [hm6 _ (hal d hd).1 ((rwords_ne (hRP.align d hd) hA).2 hdr).1 (fun e => (hfarS sc hsc d hd).1 e.symm)
        (rwords_ne (hRP.align d hd) hA).1]
      exact hm3 _ (hal d hd).1 (fun e he => (rwords_ne (hRP.align d hd) (hRP.align e (hhR e he))).1)
    have hN6 : ∀ d ∈ R, d ≠ r → (Lst sc).head? ≠ some d → L.mem s6 (rNextA d) = L.mem s (rNextA d) := by
      intro d hd hdr hnh
      rw [hm6 _ (hal d hd).2 (fun e => (rwords_ne hA (hRP.align d hd)).1 e.symm)
        (fun e => (hfarS sc hsc d hd).2 e.symm) ((rwords_ne (hRP.align d hd) hA).2 hdr).2]
      exact hm3 _ (hal d hd).2 (fun e he => ((rwords_ne (hRP.align d hd) (hRP.align e (hhR e he))).2
        (fun h' => hnh (h' ▸ he))).2)
    have hCRB : CallRel (L.mem s6) R C σB (Function.update Lst sc (r :: Lst sc)) := by
      refine hCR.push hsc hr hdet hiso hP6 hN6 (fun d hh => ?_) ?_ ?_ ?_
        (fun q hq hne => ?_) hk hkscB (fun q hq hne => ?_) hkr hkrB (fun d x hh hkd => ?_)
        (fun d hd hdr hnh => ?_)
      · have hdR := hhR d hh
        have hdr := hhr d hh
        rw [hm6 _ (hal d hdR).2 (fun e => (rwords_ne hA (hRP.align d hdR)).1 e.symm)
          (fun e => (hfarS sc hsc d hdR).2 e.symm) ((rwords_ne (hRP.align d hdR) hA).2 hdr).2]
        exact hmH3 d hh
      · rw [hs6, hwr hNr hPr (by rw [rNextA_val hA, rPrevA_val hA]; omega),
          hwr haP hPr (fun e => (hfarS sc hsc r hr).1 e)]
        exact L.mem_wr_same hPr
      · exact L.mem_wr_same hNr
      · rw [hs6, hwr hNr haP (fun e => (hfarS sc hsc r hr).2 e.symm)]; exact L.mem_wr_same haP
      · obtain ⟨haq, -, -⟩ := sc_reply_word hS hq
        rw [hm6 _ haq (fun e => (hfarS q hq r hr).1 e) (hSne q hq hne) (fun e => (hfarS q hq r hr).2 e)]
        exact hm3 _ haq (fun e he => (hfarS q hq e (hhR e he)).2)
      · have hqr : q.bv ≠ r.bv := fun e => by
          obtain ⟨Q, R', hc, hs⟩ := hS.lists
          obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
          rw [e, hkr] at hkq; cases hkq
        rw [hkB _ hqr, hkB1 _ (bv_ne hne), hkA q.bv (fun d hh e => by
          obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d hh)
          obtain ⟨Q, R', hc, hs⟩ := hS.lists
          obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
          rw [e, hkd] at hkq; cases hkq)]
      · have hdR := hhR d hh
        rw [hkB _ (fun e => hhr d hh (eq_of_bv e)), hkB1 _ (fun e => hnh_sc d hh e.symm)]
        exact hkh3 d x hh hkd
      · have hdsc : d.bv ≠ sc.bv := fun e => by
          obtain ⟨xd, hkd, -⟩ := hCR.reply d hd; rw [e, hk] at hkd; cases hkd
        rw [hkB _ (bv_ne hdr), hkB1 _ hdsc, hkA d.bv (fun d' hh' e => hnh (by rw [hh', ← eq_of_bv e]))]
    -- the donation
    have hkfB : σB.kheap f.bv = some (.tcb xf) := by
      rw [hkB _ (Ne.symm hrf), hkB1 _ (Ne.symm hpf), hkA _ (fun d hh e => by
        obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d hh); rw [← e, hkf] at hkd; cases hkd)]
      exact hkf
    have hktB : σB.kheap t.bv = some (.tcb xt) := by
      rw [hkB _ (Ne.symm hrt), hkB1 _ (Ne.symm hpt), hkA _ (fun d hh e => by
        obtain ⟨xd, hkd, -⟩ := hCR.reply d (hhR d hh); rw [← e, hkt] at hkd; cases hkd)]
      exact hkt
    have hrelB : inClassR xt.tcbState xt.tcbFault → Fl4Spec.scActive { y with scReplies := r.bv :: y.scReplies } = true →
        released σB { y with scReplies := r.bv :: y.scReplies } := fun h1 h2 => by
      have := hrel h1 h2
      unfold released at this ⊢
      rw [show σB.curTime = σ.curTime from htm3]; exact this
    refine WP.spec_mono (donate_bound_refines s6 a σB hS6 hR6 hNB hIB hsc hsc0 hkscB hf hyf hkfB ht hktB hxt0 hft
      hrelB) ?_
    rintro res ⟨σ', hdon, ha, hS', hR', hN', hI', hw', hksc', hko', hkf', hkt', -, -, -⟩
    obtain ⟨cw1, cw2⟩ := callWords_of_dfoot hS6 hRP6 hsc hw'
    have hw6 : WritesIn st s s6 (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) :=
      tr (tr (tr hw3 (cwr hPr (Or.inl ⟨r, hr, Or.inr rfl⟩))) (cwr haP (Or.inr ⟨sc, hsc, rfl⟩)))
        (cwr hNr (Or.inl ⟨r, hr, Or.inl rfl⟩))
    have hwD : WritesIn st s res.1 (fun b => KFoot st T N C c s σ b ∨ CallW' R C b) :=
      tr hw6 (hw'.mono fun b hb => by
        rcases hb with hb | rfl
        · exact Or.inl (KFoot.of_sfoot ((SFoot.ksb hw6.1).1 hb))
        · exact Or.inl (KFoot.of_sw (sw_hdr hS hsc (K := 24#u64) (by simp) (by simp) (by decide))))
    have hqC : ∀ q ∈ C, q.bv ≠ f.bv ∧ q.bv ≠ t.bv := fun q hq => by
      obtain ⟨Q, R', hc, hs⟩ := hS.lists
      obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
      exact ⟨fun e => (by rw [e, hkf] at hkq; cases hkq), fun e => (by rw [e, hkt] at hkq; cases hkq)⟩
    refine ⟨ha, σ', ?_, hS', hR', hN', hI', ?_, ?_, ?_, hwD,
      fun d hd hdr hnh => ⟨(cw2 d hd).2.trans (hN6 d hd hdr hnh), (cw2 d hd).1.trans (hP6 d hd hdr)⟩⟩
    · have hbind : Fl4Spec.bindScReply (Z := Unit) sc.bv r.bv σ = ({((), σB)}, False) := by
        unfold Fl4Spec.bindScReply
        rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _)]
        have tail : (do
            Fl4Spec.setScObjRef Fl4Spec.scRepliesUpdate sc.bv (r.bv :: y.scReplies)
            Fl4Spec.setReplyObjRef Fl4Spec.replyScUpdate r.bv (some sc.bv) : Fl4Spec.SMonad Unit Unit) σA =
            ({((), σB)}, False) := by
          show (Fl4Spec.updateSchedContext sc.bv _ >>= _) σA = _
          rw [nd_bind_one (updateSchedContext_eq hk3 _)]
          exact setReplySc_eq (some sc.bv) hkrB1
        rcases hcase with ⟨hL0, rfl⟩ | ⟨d, l, x, hL0, hkd, rfl⟩
        · rw [hyL, hL0]; rw [hyL, hL0] at tail; exact tail
        · rw [hyL, hL0]; rw [hyL, hL0] at tail
          simp only [List.map_cons]
          rw [nd_bind_one (setReplySc_eq none hkd)]; exact tail
      rw [nd_bind_one hbind]; exact hdon
    · refine hCRB.frame cw1 cw2 (fun q hq y0 n0 hy0 => ?_) (fun d hd x hx => ?_)
      · by_cases e : q = sc
        · subst e; rw [hkscB] at hy0; cases hy0; exact ⟨_, hksc', rfl⟩
        · exact ⟨y0, by rw [hko' _ (bv_ne e) (hqC q hq).1 (hqC q hq).2]; exact hy0, rfl⟩
      · have hdsc : d.bv ≠ sc.bv := fun e => by rw [e, hkscB] at hx; cases hx
        have hdf : d.bv ≠ f.bv := fun e => by rw [e, hkfB] at hx; cases hx
        have hdt : d.bv ≠ t.bv := fun e => by rw [e, hktB] at hx; cases hx
        exact ⟨x, by rw [hko' _ hdsc hdf hdt]; exact hx, rfl⟩
    · refine hRP6.frame hw'.1 (fun q x' n' hq => ?_)
      by_cases e : q = sc.bv
      · subst e; rw [hksc'] at hq; cases hq; exact ⟨_, hkscB⟩
      · by_cases ef : q = f.bv
        · subst ef; rw [hkf'] at hq; cases hq
        · by_cases et : q = t.bv
          · subst et; rw [hkt'] at hq; cases hq
          · rw [hko' q e ef et] at hq; exact ⟨x', hq⟩
    · intro d hd hfd
      obtain ⟨xd, hkd, -⟩ := hCR.reply d hd
      have hfσ : Free σ d := by
        obtain ⟨x', hk', hx'⟩ := hfd
        have hdsc : d.bv ≠ sc.bv := fun e => by rw [e, hk] at hkd; cases hkd
        have hdf : d.bv ≠ f.bv := fun e => by rw [e, hkf] at hkd; cases hkd
        have hdt : d.bv ≠ t.bv := fun e => by rw [e, hkt] at hkd; cases hkd
        rw [hko' _ hdsc hdf hdt] at hk'
        by_cases er : d = r
        · subst er; rw [hkrB] at hk'; cases hk'; rw [hkr] at hkd; cases hkd; exact ⟨_, hkr, hx'⟩
        rw [hkB _ (bv_ne er), hkB1 _ hdsc] at hk'
        by_cases eh : (Lst sc).head? = some d
        · rw [hkh3 d xd eh hkd] at hk'; cases hk'; exact ⟨xd, hkd, hx'⟩
        · rw [hkA _ (fun d' hh' e => eh (by rw [hh', ← eq_of_bv e]))] at hk'
          exact ⟨x', hk', hx'⟩
      have hdr : d ≠ r := fun e => hnf (e ▸ hfσ)
      obtain ⟨hdet', h0n, h0p⟩ := hRF d hd hfσ
      have hnh : (Lst sc).head? ≠ some d := fun hh => hdet' sc hsc (List.mem_of_mem_head? hh)
      refine ⟨fun q hq hm => ?_, by rw [(cw2 d hd).2, hN6 d hd hdr hnh]; exact h0n,
        by rw [(cw2 d hd).1, hP6 d hd hdr]; exact h0p⟩
      by_cases e : q = sc
      · subst e
        simp only [Function.update_self, List.mem_cons] at hm
        rcases hm with hm | hm
        · exact hdr hm
        · exact hdet' _ hq hm
      · simp only [ne_eq, e, not_false_eq_true, Function.update_of_ne] at hm
        exact hdet' q hq hm
  refine WP.spec_bind (obj.Sc.reply.val s sc) ?_
  intro i2 hi2
  rw [hLw.1] at hi2
  subst hi2
  by_cases hL : Lst sc = []
  · have hb : ((Lst sc).headD 0#u64 != 0#u64) = false := by rw [hL]; rfl
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact cont s σ hS hR hN hI rfl (fun q _ => rfl) (fun d x hh => by rw [hL] at hh; cases hh) rfl
      (Or.inl ⟨hL, rfl⟩) (fun b _ _ => rfl) (fun d hh => by rw [hL] at hh; cases hh) (WritesIn.refl _ _)
  · obtain ⟨d, l, hL'⟩ := List.exists_cons_of_ne_nil hL
    have hhd : (Lst sc).headD 0#u64 = d := by rw [hL']; rfl
    have hhh : (Lst sc).head? = some d := by rw [hL']; rfl
    have hdR : d ∈ R := hhR d hhh
    have hAd := hRP.align d hdR
    have hb : ((Lst sc).headD 0#u64 != 0#u64) = true := by rw [hhd]; simpa using hAd.2.1
    rw [hb]
    simp only [↓reduceIte]
    refine WP.spec_bind (obj.Reply.set_next.val0 s _ r) ?_
    rintro s3 rfl
    rw [and_not1 r (hev r hr), or0]
    obtain ⟨xd, hkd, -⟩ := hCR.reply d hdR
    have hNd : Aligned (rNextA ((Lst sc).headD 0#u64)) := by rw [hhd]; exact (hal d hdR).2
    have hS3 := (hS.wr_far hNd (by rw [hhd]; exact hRP.far hdR (Or.inr (rNextA_val hAd))) r).stableW
      (WritesIn.refl _ _) (NtfnStepW.updReply hkd { xd with replySc := none })
    have hR3 : NtfnStateRel N T (L.mem (L.wr s (rNextA ((Lst sc).headD 0#u64)) r))
        (updK σ d.bv (.reply { xd with replySc := none })) :=
      hR.frame hP (footEq_wr_far hP hNd (fun n hn => by have := hRP.ntfn d hdR n hn; rw [hhd, rNextA_val hAd]; omega)
        (fun t ht => by have := hRP.tcb d hdR t ht; rw [hhd, rNextA_val hAd]; omega) _) (KView.updReply hkd _)
    refine cont _ _ hS3 hR3 (hN.updReply hkd _) (hI.updReply hkd) (by simp)
      (fun q hq => by
        have : q ≠ d.bv := hq d hhh
        simp [updK, this])
      (fun d' x hh hkd' => by
        rw [hhh] at hh; cases hh; rw [hkd] at hkd'; cases hkd'; simp [updK])
      rfl (Or.inr ⟨d, l, xd, hL', hkd, rfl⟩)
      (fun b hb' hne => L.mem_wr_ne hNd hb' (by rw [hhd]; exact (hne d hhh).symm))
      (fun d' hh => by rw [hhh] at hh; cases hh; rw [← hhd]; exact L.mem_wr_same hNd)
      (cwr hNd (Or.inl ⟨d, hdR, Or.inl (by rw [hhd])⟩))

end

end

end Fl4Proofs.P3.Sched

/-! ## The spec's state after the donating push -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- The old head of a call stack loses its SC link (`bind_sc_reply`'s first
step). -/
def hdClr (σ : State Unit) : List ObjRef → State Unit
  | [] => σ
  | h :: _ => match σ.kheap h with
    | some (.reply x) => updK σ h (.reply { x with replySc := none })
    | _ => σ

/-- **The spec's `bind_sc_reply p w`** (`y`, `n` the SC's, `xw` the reply's). -/
def bdSt (σ : State Unit) (p w : ObjRef) (y : SchedContext) (n : Nat) (xw : Reply) : State Unit :=
  updK (updSc (hdClr σ y.scReplies) p { y with scReplies := w :: y.scReplies } n) w
    (.reply { xw with replySc := some p })

/-- **The donating push's state**: `bind_sc_reply`, then the donation of the
current thread `t`'s SC `p` to `d`. -/
def pdSt (σ : State Unit) (t d p w : ObjRef) (xt xd : Tcb) (xw : Reply) (y : SchedContext) (n : Nat) :
    State Unit :=
  dnSt (bdSt σ p w y n xw) t d p xt xd { y with scReplies := w :: y.scReplies } n

theorem hdClr_rec (σ : State Unit) (l : List ObjRef) : ∃ k, hdClr σ l = { σ with kheap := k } := by
  cases l with
  | nil => exact ⟨σ.kheap, rfl⟩
  | cons h l =>
    simp only [hdClr]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨σ.kheap, rfl⟩

theorem bd_rec (σ : State Unit) (p w : ObjRef) (y : SchedContext) (n : Nat) (xw : Reply) :
    ∃ k, bdSt σ p w y n xw = { σ with kheap := k } := by
  obtain ⟨k, hk⟩ := hdClr_rec σ y.scReplies
  unfold bdSt
  rw [hk]
  exact ⟨_, rfl⟩

theorem hdClr_ko {σ : State Unit} {l : List ObjRef} {q : ObjRef} (hq : ∀ h t, l = h :: t → q ≠ h) :
    (hdClr σ l).kheap q = σ.kheap q := by
  cases l with
  | nil => rfl
  | cons h t =>
    simp only [hdClr]
    split
    · simp [updK, hq h t rfl]
    · rfl

theorem hdClr_kh {σ : State Unit} {h : ObjRef} {t : List ObjRef} {x : Reply} (hk : σ.kheap h = some (.reply x)) :
    (hdClr σ (h :: t)).kheap h = some (.reply { x with replySc := none }) := by
  simp only [hdClr, hk]; simp [updK]

section Bd
variable {σ : State Unit} {p w : ObjRef} {y : SchedContext} {n : Nat} {xw : Reply}

theorem bd_kw : (bdSt σ p w y n xw).kheap w = some (.reply { xw with replySc := some p }) := by
  simp [bdSt, updK]

theorem bd_kp (hwp : w ≠ p) :
    (bdSt σ p w y n xw).kheap p = some (.schedContext { y with scReplies := w :: y.scReplies } n) := by
  simp [bdSt, updK, Ne.symm hwp]

theorem bd_ko {q : ObjRef} (h1 : q ≠ p) (h2 : q ≠ w) (h3 : ∀ h t, y.scReplies = h :: t → q ≠ h) :
    (bdSt σ p w y n xw).kheap q = σ.kheap q := by
  simp only [bdSt, updK, Function.update_of_ne h2, Function.update_of_ne h1]
  exact hdClr_ko h3

theorem bd_kh {h : ObjRef} {t : List ObjRef} (hr : y.scReplies = h :: t) {x : Reply}
    (hk : σ.kheap h = some (.reply x)) (h1 : h ≠ p) (h2 : h ≠ w) :
    (bdSt σ p w y n xw).kheap h = some (.reply { x with replySc := none }) := by
  simp only [bdSt, updK, Function.update_of_ne h2, Function.update_of_ne h1, hr]
  exact hdClr_kh hk

theorem bd_ct : (bdSt σ p w y n xw).curThread = σ.curThread := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]
theorem bd_csc : (bdSt σ p w y n xw).curSc = σ.curSc := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]
theorem bd_act : (bdSt σ p w y n xw).schedulerAction = σ.schedulerAction := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]
theorem bd_rel : (bdSt σ p w y n xw).releaseQueue = σ.releaseQueue := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]
theorem bd_rq : (bdSt σ p w y n xw).readyQueues = σ.readyQueues := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]
theorem bd_idle : (bdSt σ p w y n xw).idleThread = σ.idleThread := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]
theorem bd_isc : (bdSt σ p w y n xw).idleSc = σ.idleSc := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]
theorem bd_cons : (bdSt σ p w y n xw).consumedTime = σ.consumedTime := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]
theorem bd_tm : (bdSt σ p w y n xw).curTime = σ.curTime := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]

variable (hk : σ.kheap p = some (.schedContext y n)) (hkw : σ.kheap w = some (.reply xw)) (hwp : w ≠ p)
  (hh : ∀ h t, y.scReplies = h :: t → h ≠ p ∧ h ≠ w ∧ ∃ x, σ.kheap h = some (.reply x))
include hk hkw hwp hh

/-- **`bind_sc_reply`** (module docstring). -/
theorem bindScReply_eq : bindScReply (Z := Unit) p w σ = ({((), bdSt σ p w y n xw)}, False) := by
  have tail : ∀ σA : State Unit, σA.kheap p = some (.schedContext y n) → σA.kheap w = some (.reply xw) →
      (do
        setScObjRef scRepliesUpdate p (w :: y.scReplies)
        setReplyObjRef replyScUpdate w (some p) : SMonad Unit Unit) σA =
      ({((), updK (updSc σA p { y with scReplies := w :: y.scReplies } n) w
        (.reply { xw with replySc := some p }))}, False) := by
    intro σA hkA hkwA
    show (updateSchedContext p _ >>= _) σA = _
    rw [nd_bind_one (updateSchedContext_eq hkA _)]
    have : (updSc σA p { y with scReplies := w :: y.scReplies } n).kheap w = some (.reply xw) := by
      simp [updK, hwp, hkwA]
    exact setReplySc_eq (some p) this
  unfold bindScReply
  rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _)]
  unfold bdSt
  cases hr : y.scReplies with
  | nil =>
    rw [hr] at tail
    exact tail σ hk hkw
  | cons h l =>
    rw [hr] at tail
    obtain ⟨hp, hw, x, hkh⟩ := hh h l hr
    simp only [hdClr, hkh]
    rw [nd_bind_one (setReplySc_eq none hkh)]
    exact tail _ (by simp [updK, Ne.symm hp, hk]) (by simp [updK, Ne.symm hw, hkw])

/-- What `bind_sc_reply` keeps (`SOK` without the call stacks). -/
theorem bd_sok : SOK (true, false) σ (bdSt σ p w y n xw) := by
  have h1 : SOK (true, false) σ (hdClr σ y.scReplies) := by
    cases hr : y.scReplies with
    | nil => exact SOK.refl _ _
    | cons h l =>
      obtain ⟨-, -, x, hkh⟩ := hh h l hr
      simp only [hdClr, hkh]
      exact SOK.upd hkh (by simp [PK])
  have hk1 : (hdClr σ y.scReplies).kheap p = some (.schedContext y n) := by
    rw [hdClr_ko (fun h t e => (hh h t e).1.symm)]; exact hk
  have h2 := SOK.upd (f := (true, false)) hk1 (o' := .schedContext { y with scReplies := w :: y.scReplies } n)
    (by simp [PK])
  have hkw2 : (updSc (hdClr σ y.scReplies) p { y with scReplies := w :: y.scReplies } n).kheap w =
      some (.reply xw) := by
    simp only [updK, Function.update_of_ne hwp]
    rw [hdClr_ko (fun h t e => (hh h t e).2.1.symm)]; exact hkw
  have h3 := SOK.upd (f := (true, false)) hkw2 (o' := .reply { xw with replySc := some p }) (by simp [PK])
  exact (h1.trans h2).trans h3

end Bd

/-- `test_reschedule` of the current thread, no switch pending. -/
theorem testReschedule_curN {σ : State Unit} {t : ObjRef} (hct : t = σ.curThread)
    (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u) :
    testReschedule (Z := Unit) t σ = ({((), { σ with schedulerAction := .chooseNewThread })}, False) := by
  unfold testReschedule
  rw [nd_gets_bind, nd_gets_bind, nd_pure_bind']
  unfold NonDet.when
  rw [if_pos (Or.inl hct)]
  exact rescheduleRequired_nsw hnsw

/-- **The spec's donation of the current thread's SC** (in no queue, no
switch pending: SendDon's `donate_cur_eq` without the resume action). -/
theorem donate_curN_eq {σ : State Unit} {t d p : ObjRef} {xt xd : Tcb} {y : SchedContext} {n : Nat}
    (hkt : σ.kheap t = some (.tcb xt)) (hkd : σ.kheap d = some (.tcb xd))
    (hkp : σ.kheap p = some (.schedContext y n)) (hyt : y.scTcb = some t) (htd : t ≠ d) (hpt : p ≠ t)
    (hpd : p ≠ d) (hct : t = σ.curThread) (hnq : NotQueued σ t)
    (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u) :
    schedContextDonate (Z := Unit) p d σ = ({((), dnSt σ t d p xt xd y n)}, False) := by
  have hQ : setQ σ xt.tcbDomain xt.tcbPriority (tcbSchedDequeue t (σ.readyQueues xt.tcbDomain xt.tcbPriority)) = σ := by
    have h1 : tcbSchedDequeue t (σ.readyQueues xt.tcbDomain xt.tcbPriority) =
        σ.readyQueues xt.tcbDomain xt.tcbPriority := by
      unfold tcbSchedDequeue
      exact List.filter_eq_self.2 fun a ha => by
        have : t ≠ a := fun e => hnq.1 _ _ (e ▸ ha)
        simpa using this
    rw [h1, setQ_self]
  set σ1 : State Unit := { updK σ t (.tcb { xt with tcbSchedContext := none }) with
    schedulerAction := .chooseNewThread } with hσ1
  have hkp1 : σ1.kheap p = some (.schedContext y n) := by simp [σ1, updK, hpt, hkp]
  have hkd2 : (updSc σ1 p { y with scTcb := some d } n).kheap d = some (.tcb xd) := by
    simp [σ1, updK, Ne.symm hpd, Ne.symm htd, hkd]
  unfold schedContextDonate
  rw [nd_bind_one (getScObjRef_eq hkp _), hyt]
  unfold NonDet.when
  rw [if_pos (by simp)]
  have hin : (do
      let fromTptr ← NonDet.assertOpt (some t)
      tcbSchedAction tcbSchedDequeue fromTptr
      tcbReleaseRemove fromTptr
      setTcbObjRef tcbSchedContextUpdate fromTptr none
      testReschedule fromTptr : SMonad Unit Unit) σ = ({((), σ1)}, False) := by
    rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ = ({(t, σ)}, False) from rfl)]
    rw [nd_bind_one (tcbSchedAction_gen hkt _), hQ]
    rw [nd_bind_one (tcbReleaseRemove_not hnq.2)]
    show (threadSet _ t >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hkt)]
    exact testReschedule_curN hct (fun u e => hnsw u e)
  rw [nd_bind_one hin]
  show (updateSchedContext p _ >>= _) σ1 = _
  rw [nd_bind_one (updateSchedContext_eq hkp1 _)]
  show threadSet _ d _ = _
  exact threadSet_eq _ hkd2

/-- **The spec's donating push** (`bind_sc_reply`, then the donation of the
current thread's SC). -/
theorem pd_eq {σ : State Unit} {t d p w : ObjRef} {xt xd : Tcb} {xw : Reply} {y : SchedContext} {n : Nat}
    (hkt : σ.kheap t = some (.tcb xt)) (hkd : σ.kheap d = some (.tcb xd))
    (hk : σ.kheap p = some (.schedContext y n)) (hkw : σ.kheap w = some (.reply xw)) (hwp : w ≠ p)
    (hh : ∀ h l, y.scReplies = h :: l → h ≠ p ∧ h ≠ w ∧ ∃ x, σ.kheap h = some (.reply x))
    (hyt : y.scTcb = some t) (htd : t ≠ d) (hpt : p ≠ t) (hpd : p ≠ d) (hwt : w ≠ t) (hwd : w ≠ d)
    (hct : t = σ.curThread) (hnq : NotQueued σ t) (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u) :
    (do
      bindScReply (Z := Unit) p w
      schedContextDonate (Z := Unit) p d) σ = ({((), pdSt σ t d p w xt xd xw y n)}, False) := by
  have hnt : ∀ h l, y.scReplies = h :: l → t ≠ h := fun h l e e' => by
    obtain ⟨-, -, x, hx⟩ := hh h l e; rw [← e', hkt] at hx; cases hx
  have hnd : ∀ h l, y.scReplies = h :: l → d ≠ h := fun h l e e' => by
    obtain ⟨-, -, x, hx⟩ := hh h l e; rw [← e', hkd] at hx; cases hx
  rw [nd_bind_one (bindScReply_eq hk hkw hwp hh)]
  exact donate_curN_eq (by rw [bd_ko (Ne.symm hpt) (Ne.symm hwt) hnt]; exact hkt)
    (by rw [bd_ko (Ne.symm hpd) (Ne.symm hwd) hnd]; exact hkd) (bd_kp hwp) hyt htd hpt hpd
    (by rw [bd_ct]; exact hct) ⟨by rw [bd_rq]; exact hnq.1, by rw [bd_rel]; exact hnq.2⟩
    (by rw [bd_act]; exact hnsw)


section Bd2
variable {σ : State Unit} {p w : ObjRef} {y : SchedContext} {n : Nat} {xw : Reply}

theorem bd_arch : (bdSt σ p w y n xw).archState = σ.archState := by
  obtain ⟨k, hk⟩ := bd_rec σ p w y n xw; rw [hk]

variable (hk : σ.kheap p = some (.schedContext y n)) (hkw : σ.kheap w = some (.reply xw)) (hwp : w ≠ p)
  (hh : ∀ h t, y.scReplies = h :: t → h ≠ p ∧ h ≠ w ∧ ∃ x, σ.kheap h = some (.reply x))
include hk hkw hwp hh

/-- An object other than a reply, not at `p`, is kept by `bind_sc_reply`. -/
theorem bd_oth {q : ObjRef} {o : KernelObject} (ho : ∀ x, o ≠ .reply x) (hqp : q ≠ p)
    (hq : σ.kheap q = some o) : (bdSt σ p w y n xw).kheap q = some o := by
  have hqw : q ≠ w := fun e => by rw [e, hkw] at hq; exact ho _ (Option.some.inj hq).symm
  rw [bd_ko hqp hqw (fun h t hr e => by
    obtain ⟨-, -, x, hx⟩ := hh h t hr; rw [← e, hq] at hx; exact ho _ (Option.some.inj hx))]
  exact hq

theorem bd_scB {q : ObjRef} {y' : SchedContext} {m : Nat}
    (hq : (bdSt σ p w y n xw).kheap q = some (.schedContext y' m)) :
    (q = p ∧ y' = { y with scReplies := w :: y.scReplies } ∧ m = n) ∨ σ.kheap q = some (.schedContext y' m) := by
  by_cases e1 : q = p
  · subst e1; rw [bd_kp hwp] at hq; cases hq; exact Or.inl ⟨rfl, rfl, rfl⟩
  by_cases e2 : q = w
  · subst e2; rw [bd_kw] at hq; cases hq
  by_cases e3 : ∃ h t, y.scReplies = h :: t ∧ q = h
  · obtain ⟨h, t, hr, rfl⟩ := e3
    obtain ⟨h1, h2, x, hx⟩ := hh q t hr
    rw [bd_kh hr hx h1 h2] at hq; cases hq
  rw [bd_ko e1 e2 (fun h t hr e => e3 ⟨h, t, hr, e⟩)] at hq
  exact Or.inr hq

theorem bd_tcbB {q : ObjRef} {x : Tcb} (hq : (bdSt σ p w y n xw).kheap q = some (.tcb x)) :
    σ.kheap q = some (.tcb x) := by
  by_cases e1 : q = p
  · subst e1; rw [bd_kp hwp] at hq; cases hq
  by_cases e2 : q = w
  · subst e2; rw [bd_kw] at hq; cases hq
  by_cases e3 : ∃ h t, y.scReplies = h :: t ∧ q = h
  · obtain ⟨h, t, hr, rfl⟩ := e3
    obtain ⟨h1, h2, x, hx⟩ := hh q t hr
    rw [bd_kh hr hx h1 h2] at hq; cases hq
  rw [bd_ko e1 e2 (fun h t hr e => e3 ⟨h, t, hr, e⟩)] at hq
  exact hq

theorem bd_reply {q : ObjRef} {x : Reply} (hq : σ.kheap q = some (.reply x)) :
    ∃ x', (bdSt σ p w y n xw).kheap q = some (.reply x') ∧ x'.replyTcb = x.replyTcb := by
  have hqp : q ≠ p := fun e => by rw [e, hk] at hq; cases hq
  by_cases e2 : q = w
  · subst e2; rw [hkw] at hq; cases hq; exact ⟨_, bd_kw, rfl⟩
  by_cases e3 : ∃ h t, y.scReplies = h :: t ∧ q = h
  · obtain ⟨h, t, hr, rfl⟩ := e3
    obtain ⟨h1, h2, -⟩ := hh q t hr
    exact ⟨_, bd_kh hr hq h1 h2, rfl⟩
  exact ⟨x, by rw [bd_ko hqp e2 (fun h t hr e => e3 ⟨h, t, hr, e⟩)]; exact hq, rfl⟩

theorem bd_idleOK (hO : IdleOK σ) : IdleOK (bdSt σ p w y n xw) := by
  obtain ⟨x, h1, h2, h3, h4⟩ := hO
  have hip : σ.idleThread ≠ p := fun e => by rw [e, hk] at h1; cases h1
  exact ⟨x, by rw [bd_idle]; exact bd_oth hk hkw hwp hh (fun _ e => by cases e) hip h1, by rw [bd_isc]; exact h2, h3,
    by rw [bd_idle, bd_rel]; exact h4⟩

theorem bd_off (hO : OffOK σ) (hpc : σ.curSc = p) : OffOK (bdSt σ p w y n xw) := by
  intro h0 y' m hy ha
  rw [bd_csc, hpc, bd_kp hwp] at hy; cases hy
  rw [bd_cons] at h0 ⊢; rw [bd_tm]
  exact hO h0 y n (by rw [hpc]; exact hk) (fun h => ha (by rw [bd_csc, bd_isc]; exact h))

theorem bd_bsa (hB : BlockedScActive σ) (hya : scActive y = true) : BlockedScActive (bdSt σ p w y n xw) := by
  refine ⟨fun q y' m u xu hq hyu hku hqd => ?_, fun q y' m hq hne => ?_⟩
  · rcases bd_scB hk hkw hwp hh hq with ⟨rfl, rfl, rfl⟩ | hq'
    · exact hya
    · exact hB.tcb q y' m u xu hq' hyu (bd_tcbB hk hkw hwp hh hku) hqd
  · rcases bd_scB hk hkw hwp hh hq with ⟨rfl, rfl, rfl⟩ | hq'
    · exact hya
    · exact hB.replies q y' m hq' hne

end Bd2

section Pd
variable {σ : State Unit} {t d p w : ObjRef} {xt xd : Tcb} {xw : Reply} {y : SchedContext} {n : Nat}

theorem pd_act : (pdSt σ t d p w xt xd xw y n).schedulerAction = .chooseNewThread := rfl
theorem pd_ct : (pdSt σ t d p w xt xd xw y n).curThread = σ.curThread := @bd_ct σ p w y n xw
theorem pd_csc : (pdSt σ t d p w xt xd xw y n).curSc = σ.curSc := @bd_csc σ p w y n xw
theorem pd_rel : (pdSt σ t d p w xt xd xw y n).releaseQueue = σ.releaseQueue := @bd_rel σ p w y n xw
theorem pd_rq : (pdSt σ t d p w xt xd xw y n).readyQueues = σ.readyQueues := @bd_rq σ p w y n xw
theorem pd_idle : (pdSt σ t d p w xt xd xw y n).idleThread = σ.idleThread := @bd_idle σ p w y n xw
theorem pd_isc : (pdSt σ t d p w xt xd xw y n).idleSc = σ.idleSc := @bd_isc σ p w y n xw
theorem pd_tm : (pdSt σ t d p w xt xd xw y n).curTime = σ.curTime := @bd_tm σ p w y n xw
theorem pd_arch : (pdSt σ t d p w xt xd xw y n).archState = σ.archState := @bd_arch σ p w y n xw
theorem pd_kd : (pdSt σ t d p w xt xd xw y n).kheap d = some (.tcb { xd with tcbSchedContext := some p }) :=
  @dn_kd (bdSt σ p w y n xw) t d p xt xd { y with scReplies := w :: y.scReplies } n
theorem pd_ko {q : ObjRef} (h1 : q ≠ t) (h2 : q ≠ d) (h3 : q ≠ p) :
    (pdSt σ t d p w xt xd xw y n).kheap q = (bdSt σ p w y n xw).kheap q :=
  @dn_ko (bdSt σ p w y n xw) t d p xt xd { y with scReplies := w :: y.scReplies } n q h1 h2 h3

end Pd

/-- **The donation after `bind_sc_reply`** (SendDon's `dnSt`). -/
theorem bd_donate_eq {σ : State Unit} {t d p w : ObjRef} {xt xd : Tcb} {xw : Reply} {y : SchedContext} {n : Nat}
    (hkt : σ.kheap t = some (.tcb xt)) (hkd : σ.kheap d = some (.tcb xd))
    (hk : σ.kheap p = some (.schedContext y n)) (hkw : σ.kheap w = some (.reply xw)) (hwp : w ≠ p)
    (hh : ∀ h l, y.scReplies = h :: l → h ≠ p ∧ h ≠ w ∧ ∃ x, σ.kheap h = some (.reply x))
    (hyt : y.scTcb = some t) (htd : t ≠ d) (hpt : p ≠ t) (hpd : p ≠ d)
    (hct : t = σ.curThread) (hnq : NotQueued σ t) (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u) :
    schedContextDonate (Z := Unit) p d (bdSt σ p w y n xw) = ({((), pdSt σ t d p w xt xd xw y n)}, False) :=
  donate_curN_eq (bd_oth hk hkw hwp hh (fun _ e => by cases e) (Ne.symm hpt) hkt)
    (bd_oth hk hkw hwp hh (fun _ e => by cases e) (Ne.symm hpd) hkd) (bd_kp hwp) hyt htd hpt hpd
    (by rw [bd_ct]; exact hct) ⟨by rw [bd_rq]; exact hnq.1, by rw [bd_rel]; exact hnq.2⟩
    (by rw [bd_act]; exact hnsw)


/-- **The spec's donating `reply_push`**: the link and block (`pushSt`),
then `bind_sc_reply` and the donation of the caller's SC `sc`. -/
theorem replyPush_don_eq {σ : State Unit} {t d r sc : ObjRef} {xt xd : Tcb} {xr : Reply}
    (hkt : σ.kheap t = some (.tcb xt)) (hkd : σ.kheap d = some (.tcb xd)) (hkr : σ.kheap r = some (.reply xr))
    (hrt : r ≠ t) (hxt : xt.tcbSchedContext = some sc) (hxd : xd.tcbSchedContext = none) :
    replyPush (Z := Unit) t d r true σ = (do
        bindScReply (Z := Unit) sc r
        schedContextDonate (Z := Unit) sc d) (Endp.pushSt σ t r xr xt) := by
  have hkt1 : (updK σ r (.reply { xr with replyTcb := some t })).kheap t = some (.tcb xt) := by
    simp [updK, Ne.symm hrt, hkt]
  have hspec : replyPush (Z := Unit) t d r true σ =
      NonDet.when (xt.tcbSchedContext ≠ none ∧ xd.tcbSchedContext = none ∧ true = true) (do
        bindScReply (Z := Unit) (the xt.tcbSchedContext) r
        schedContextDonate (Z := Unit) (the xt.tcbSchedContext) d) (Endp.pushSt σ t r xr xt) := by
    unfold replyPush
    rw [nd_bind_one (getTcbObjRef_eq _ hkt), nd_bind_one (getTcbObjRef_eq _ hkd), nd_bind_one (setReplyTcb_eq _ hkr),
      nd_bind_one (Notif.setThreadState_eq _ hkt1)]
    rfl
  have hc : (some sc ≠ none ∧ xd.tcbSchedContext = none ∧ true = true) := by simp [hxd]
  rw [hspec, hxt]
  unfold NonDet.when
  rw [if_pos hc]
  rfl

end Spec

/-! ## The donating part of `reply_push` at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The old head of an SC's call stack** at `J`: a reply other than the SC
and than any detached reply. -/
theorem JAtZ.stackHead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sc : U64} (hsC : sc ∈ Z.C)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n)) {w : U64}
    (hdet : Detached Z.C Lst w) :
    ∀ h l, y.scReplies = h :: l → h ≠ sc.bv ∧ h ≠ w.bv ∧ ∃ x, σ.kheap h = some (.reply x) := by
  obtain ⟨⟨y0, n0, hk0, hyL⟩, hLR, -, -⟩ := J.call.stack sc hsC
  rw [hky] at hk0; cases hk0
  intro h l hr
  rw [hyL] at hr
  cases e : Lst sc with
  | nil => rw [e] at hr; cases hr
  | cons h' l' =>
    rw [e] at hr
    simp only [List.map_cons, List.cons.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hh' : h' ∈ Z.R := hLR h' (by rw [e]; exact List.mem_cons_self ..)
    obtain ⟨x, hx, -⟩ := J.call.reply h' hh'
    refine ⟨fun e' => ?_, fun e' => ?_, x, hx⟩
    · have h2 : σ.kheap sc.bv = some (.reply x) := by rw [← e']; exact hx
      rw [hky] at h2; cases h2
    · exact hdet sc hsC (by rw [e, P1.eq_of_bv e']; exact List.mem_cons_self ..)

set_option maxHeartbeats 32000000 in
/-- **The donating part of `reply_push` at `J`** (module docstring): the
current thread `t`, blocked on the reply `w` (bound to it, unlinked, on no
call stack), donates its SC `sc` (active) to `d` (`Inactive`, no SC, not
dead), both in no queue, a reschedule pending. -/
theorem JAtZ.pushDonJ (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t d w sc : U64} (ht : t ∈ Z.T) (hd : d ∈ Z.T) (hw : w ∈ Z.R) (hsC : sc ∈ Z.C) (htd : t ≠ d)
    {xt xd : Fl4Spec.Tcb} {xw : Fl4Spec.Reply} {y : Fl4Spec.SchedContext} {n : Nat}
    (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hkw : σ.kheap w.bv = some (.reply xw)) (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hst : xt.tcbState = .blockedOnReply w.bv) (hxt : xt.tcbSchedContext = some sc.bv) (hyt : y.scTcb = some t.bv)
    (hxd : xd.tcbSchedContext = none) (hsd : xd.tcbState = .inactive) (hwt : xw.replyTcb = some t.bv)
    (hct : σ.curThread = t.bv) (hcsc : σ.curSc = sc.bv) (hcn : σ.schedulerAction = .chooseNewThread)
    (hnqt : NotQueued σ t.bv) (hnqd : NotQueued σ d.bv) (hya : Fl4Spec.scActive y = true)
    (hdet : Detached Z.C Lst w) (hn0 : L.mem s (rNextA w) = 0#u64) (hp0 : L.mem s (rPrevA w) = 0#u64)
    (hdD : ∀ q ∈ D, q.bv ≠ d.bv) :
    (do
      let i2 ← obj.Sc.reply st sc s
      let s3 ← if i2 != 0#u64 then obj.Reply.set_next st i2 s w false else ok s
      let s4 ← obj.Reply.set_prev st w s3 i2
      let s5 ← obj.Sc.set_reply st sc s4 w
      let s6 ← obj.Reply.set_next st w s5 sc true
      schedcontext.donate st arI s6 a sc d) ⦃ res => res.2 = a ∧
        (do
          Fl4Spec.bindScReply (Z := Unit) sc.bv w.bv
          Fl4Spec.schedContextDonate (Z := Unit) sc.bv d.bv) σ =
          ({((), pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n)}, False) ∧
        ∃ Lst', JAtZ (L := L) arI AR Z H Cs Ac Lst' D res.1 a (pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n) ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q0, R0, hc, hs⟩ := hS.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hsc0 : sc ≠ 0#u64 := J.c0 sc hsC
  have hscH : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc y n hsc0 hky).2⟩
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hdH : d ∈ P1.Heap.tcbs H := J.zH.1 d hd
  have hwH : w ∈ P1.Heap.replies H := J.tcbs_eq.2 ▸ hw
  -- the objects apart
  have htd' : t.bv ≠ d.bv := bv_ne htd
  have hst' : sc.bv ≠ t.bv := kheap_ne hky hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hsd' : sc.bv ≠ d.bv := kheap_ne hky hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hws : w.bv ≠ sc.bv := kheap_ne hkw hky (fun _ h1 h2 => by subst h1; cases h2)
  have hwt' : w.bv ≠ t.bv := kheap_ne hkw hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hwd' : w.bv ≠ d.bv := kheap_ne hkw hkd (fun _ h1 h2 => by subst h1; cases h2)
  -- the stack's old head
  obtain ⟨⟨y0, n0, hk0, hyL⟩, hLR, -, hLw⟩ := J.call.stack sc hsC
  rw [hky] at hk0; cases hk0
  have hh : ∀ h l, y.scReplies = h :: l → h ≠ sc.bv ∧ h ≠ w.bv ∧ ∃ x, σ.kheap h = some (.reply x) := by
    intro h l hr
    rw [hyL] at hr
    cases e : Lst sc with
    | nil => rw [e] at hr; cases hr
    | cons h' l' =>
      rw [e] at hr
      simp only [List.map_cons, List.cons.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      have hh' : h' ∈ Z.R := hLR h' (by rw [e]; exact List.mem_cons_self ..)
      obtain ⟨x, hx, -⟩ := J.call.reply h' hh'
      refine ⟨fun e' => ?_, fun e' => ?_, x, hx⟩
      · have h2 : σ.kheap sc.bv = some (.reply x) := by rw [← e']; exact hx
        rw [hky] at h2; cases h2
      · exact hdet sc hsC (by rw [e, P1.eq_of_bv e']; exact List.mem_cons_self ..)
  have hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u := fun u e => by rw [hcn] at e; cases e
  have hpd := pd_eq hkt hkd hky hkw hws hh hyt htd' hst' hsd' hwt' hwd' hct.symm hnqt hnsw
  have hdn := bd_donate_eq hkt hkd hky hkw hws hh hyt htd' hst' hsd' hct.symm hnqt hnsw
  -- FL4's words at the start
  have bits : ∀ u ∈ Z.T, NotQueued σ u.bv →
      (L.mem s (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hnu
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hc.queued u hu).1 h
      apply hnu.1 0 (specPrio (L.mem s (P1.prioA u)))
      rw [hs.rq _ (hc.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hc.released u hu).1 h
      apply hnu.2
      rw [hs.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbT, hrbT⟩ := bits t ht hnqt
  obtain ⟨hqbD, hrbD⟩ := bits d hd hnqd
  have ha1 : L.actionW s = 1#u64 := by
    have h := hS.act
    rw [hcn] at h
    unfold P1.LawfulStore.actionW; rw [hc.cur]; exact h
  have hna : ∀ u ∈ Z.T, L.actionW s ≠ u := fun u hu h' => by
    rw [ha1] at h'; exact P1.notT_small hc.tcbs (by simp) (h' ▸ hu)
  have hiw : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s ≠ u := fun u hu hne h' => by
    apply hne
    rw [hs.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hc.cur] at h'
    exact congrArg _ (show nodeW st s Z.c layout.node.IDLE_THREAD = u from h').symm
  have hitd : t.bv ≠ σ.idleThread := by
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    intro e; rw [← e, hkt] at hkx; cases hkx; rw [hst] at hxs; cases hxs
  have hidd : d.bv ≠ σ.idleThread := by
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    intro e; rw [← e, hkd] at hkx; cases hkx; rw [hsd] at hxs; cases hxs
  have hsw : L.mem s (P1.scA t) = sc := by
    obtain ⟨x', hk', -, -, hscw, -⟩ := hs.tcb t ht
    rw [hkt] at hk'; cases hk'
    exact optRef_some_eq (hscw.symm.trans hxt)
  have hd0 : L.mem s (P1.scA d) = 0#u64 := by
    obtain ⟨x', hk', -, -, hscw, -⟩ := hs.tcb d hd
    rw [hkd] at hk'; cases hk'
    exact Notif.optRef_none (by rw [← hscw]; exact hxd)
  have hiA : sc ∈ Ac := by
    have hrm := SchedRel.act_sc hS hsC hky hya
    exact (J.blk.2.2.2.1.act _ hscH).2 (fun h => hrm (by rw [h]; rfl))
  have haff : L.mem s (P1.affA d) = L.mem s (P1.scCoreA sc) := by
    rw [hc.aff d hd, Fl4Proofs.P3.Sched.scCoreA_eq, hS.core sc hsC]
  have hR0 : ∀ r ∈ Z.R, r ≠ 0#u64 ∧ r.val % 2 = 0 := fun r hr =>
    ⟨(J.rp.align r hr).2.1, by have := (J.rp.align r hr).1; omega⟩
  have hiso : Isolated (L.mem s) Z.R w := J.call.isolated hR0 hw hdet hn0 hp0
  have hrel : inClassR xd.tcbState xd.tcbFault → Fl4Spec.scActive y = true → released σ y := by
    intro hc' _
    exfalso
    rw [hsd] at hc'
    rcases hc'.cls with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩
    · simp [Fl4Spec.runnable] at h
    all_goals cases h
  have hnf : ¬ Free σ w := by
    rintro ⟨x, hx, hn⟩; rw [hkw] at hx; cases hx; rw [hwt] at hn; cases hn
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := J.blk
  refine WP.spec_mono (WP.spec_and
    (push_donate_refinesW s a σ hS hR J.nsc J.inv J.call J.rp hsC hsc0 hky ht hyt hkt hd hkd hxd htd hrel hw hdet
      hiso J.rfree hnf)
    (P1.ipc.push_don.blk (Es := P1.EH H) hAT s a t d w sc Q1 R1 h1 hB1 hX1 hS1 hSg1 htH hqbT hrbT
      (hna t ht) (hiw t ht hitd) hwH hdH (Ne.symm htd) hqbD hrbD (hna d hd) (hiw d hd hidd) hsw hsc0 hiA hd0 haff)) ?_
  rintro ⟨s', a'⟩ ⟨⟨ha, σ', hsp, hS', hR', hN', hI', hCR', hRP', hRF', hw0, hwd⟩, hP1⟩
  simp only [WP.uncurry'_pair] at hP1 ha
  obtain ⟨hblk, hfoot⟩ := hP1
  subst a'
  have e' : σ' = pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n := by
    have h := hsp.symm.trans hpd
    exact congrArg Prod.snd (Set.singleton_injective (congrArg Prod.fst h))
  subst e'
  refine ⟨rfl, hpd, Function.update Lst sc (w :: Lst sc), ?_⟩
  set σ' := pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n with hσ'
  set σB := bdSt σ sc.bv w.bv y n xw with hσB
  -- the spec's step and FL4's writes
  have hK : ScTKw (fun _ => False) σ σ' :=
    NKT.of_eq (nkt_bind (nkt_bindScReply _ _) fun _ => nkt_schedContextDonate _ _) hpd
  have hW : P1.WritesIn st s s' (fun b => TFoot st Z.T Z.N Z.C Z.c s σ b ∨ CallW' Z.R Z.C b) :=
    hw0.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl h)) Or.inr
  have hX' : XTopAt (L := L) AR Z s' a σ' :=
    xtop_sc_stepCW (ct := σ.curThread) J.xtop J.ip J.nk J.ks.rep hW (hK.mono fun _ h => h.elim) hS' hR' id
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' :=
    tk_liftCW (ct := σ.curThread) J.ip hI hW (ScTKw.ofFalse (P := fun p => p = σ.curThread) hK) hS' hR'
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw0 fun b hb =>
    hb.elim (fun h => tfoot_oobj hS (Or.inl h)) (fun h => callW'_oobj J.ip hS h)
  have hSS := hF.1
  have hks : L.ksb s' = L.ksb s := hF.2
  have hwR : P1.WritesIn st s s' (RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ) :=
    J.rmW_of (hw0.mono fun b hb => hb.elim Or.inl (fun h => Or.inr (Or.inl h)))
  obtain ⟨k1, k2, kb⟩ := J.rmW_keeps hwR
  have hsok : SOK (true, false) σ σ' :=
    (bd_sok hky hkw hws hh).trans ((pres_schedContextDonate (true, false) _ _).of_eq hdn)
  have hyk : YKeep σ σ' := hsok.ykeep rfl
  have hmk : McpKeep σ σ' := hsok.mcpKeep
  have hcn' : σ'.schedulerAction = .chooseNewThread := rfl
  have hFK : FK σ σ' := ⟨pd_csc, pd_idle, pd_isc⟩
  have hIK := J.idleW_keep hS' pd_idle pd_isc
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  -- the bound-before objects at `σB`
  have hktB : σB.kheap t.bv = some (.tcb xt) := bd_oth hky hkw hws hh (fun _ e => by cases e) (Ne.symm hst') hkt
  have hkdB : σB.kheap d.bv = some (.tcb xd) := bd_oth hky hkw hws hh (fun _ e => by cases e) (Ne.symm hsd') hkd
  have hkpB : σB.kheap sc.bv = some (.schedContext { y with scReplies := w.bv :: y.scReplies } n) := bd_kp hws
  have hpc : sc.bv = σB.curSc := by rw [bd_csc, hcsc]
  -- the receivers' replies
  have hrr : RRecv (L.mem s') Z.R σ' := by
    intro d' hd' hrd
    have hrd0 := (KhRB.of_sctkw hK).recvB hrd
    obtain ⟨h1', h2'⟩ := J.rrecv d' hd' hrd0
    have hdw : d' ≠ w := by
      rintro rfl
      obtain ⟨x, t', xt', hx, ht', hxt', hrb⟩ := hrd0
      rw [hkw] at hx; cases hx; rw [hwt] at ht'; cases ht'; rw [hkt] at hxt'; cases hxt'
      rw [hst] at hrb; cases hrb
    have hdet' := detached_of_next0 J.call (fun r hr => (J.rp.align r hr).2.1) h1'
    have hnh : (Lst sc).head? ≠ some d' := fun e => hdet' sc hsC (List.mem_of_mem_head? e)
    obtain ⟨e1, e2⟩ := hwd d' hd' hdw hnh
    exact ⟨e1.trans h1', e2.trans h2'⟩
  -- the dead
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq => by
    have hdq := J.jcov.dead q hq
    have hqt : q.bv ≠ t.bv := J.notDead ht hkt (by rw [hst]; simp [tsCode]) q hq
    have hqd : q.bv ≠ d.bv := hdD q hq
    have hqs : q.bv ≠ sc.bv := fun e => J.scOwned_not_dead ht hky hyt (by rw [← P1.eq_of_bv e]; exact hdq)
    have hko : σ'.kheap q.bv = σB.kheap q.bv := pd_ko hqt hqd hqs
    refine J.deadP_keep hIR.2.2.1 hIR.1 (fun x0 hx0 _ => ?_) (fun x0 hx0 => ?_) (fun x0 hx0 => ?_)
      (fun x0 hx0 => ?_) (fun x0 m hx0 => ?_) (fun hqC => ?_)
      (fun z hz hqC K hK8 hK' => J.rmW_scOut hwR hz hqC hK8 hK') pd_idle
      (fun u hu => by rw [hcn'] at hu; cases hu) (J.yld.frame k2 hyk) (hyk.dk q.bv) hdq
    · exact ⟨x0, by rw [hko]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hqs hx0, rfl, rfl, Or.inl rfl⟩
    · rw [hko]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hqs hx0
    · exact ⟨x0, by rw [hko]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hqs hx0, Or.inl rfl, rfl,
        Or.inl rfl⟩
    · obtain ⟨x', h1', h2'⟩ := bd_reply hky hkw hws hh hx0
      exact ⟨x', by rw [hko]; exact h1', h2'⟩
    · exact ⟨x0, by rw [hko]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hqs hx0, Or.inl rfl, Or.inl rfl⟩
    · have hqsc : q ≠ sc := fun e => hqs (by rw [e])
      obtain ⟨-, -, -, hW1⟩ := J.call.stack q hqC
      obtain ⟨-, -, -, hW2⟩ := hCR'.stack q hqC
      rw [hW2.1, hW1.1, Function.update_of_ne hqsc]
  -- the scheduler after
  have hown : CurOwnW Z.T Z.C σ' :=
    dn_own hktB hkdB hkpB htd' hst' hsd' ⟨d, hd, rfl⟩ hpc (fun _ => by rw [bd_rel]; exact hnqd.2)
  have hoff : OffOK σ' := dn_off hktB hkdB hkpB htd' hst' hsd' hpc (bd_off hky hkw hws hh J.off hcsc)
  have hact : ActIdle σ' :=
    ⟨(fun u hu => by rw [hcn'] at hu; cases hu),
      dn_idleOK hktB hkdB hkpB htd' hst' hsd' (by rw [bd_idle]; exact Ne.symm hitd)
        (by rw [bd_idle]; exact Ne.symm hidd) (bd_idleOK hky hkw hws hh J.act.2)⟩
  have hbsa : BlockedScActive σ' :=
    dn_bsa hktB hkdB hkpB htd' hst' hsd' (by rw [hsd]; rfl) (bd_bsa hky hkw hws hh J.bsa hya)
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => hK.szKeep q.bv y n hq) hks (J.rmW_irq hwR) hIK.2⟩
  exact J.sc_frameS hks hSS (J.vkeep_of hwR fun b hb => J.rmW_nv hb) hK hX' hCR' hRF' hrr (J.yld.frame k2 hyk) (J.mcp.frame k1 hmk)
    (J.buf.frame kb hK.bufKeep) hRP' (J.apart.sc_frame hks hK.szKeep) hjpl (J.jcov_keep hks hSS hdead hIK)
    (J.sc_kernW hW hK hFK hX' hDbg (subset_refl D))
    (J.rmW_utc hwR hSS hK.cdt hK.orig pd_arch hDbg) hN' hI' (Or.inl hcn') hown hoff hact hbsa
    (Or.inl (by rw [hcn']; intro h; cases h)) hblk hKd hIK.1 J.zD

end

end

end Fl4Proofs.P3
