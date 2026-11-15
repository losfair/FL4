/-
P3 (DESIGN.md §9), scheduling contexts: **`reply_push`'s donation branch**
against l4v `bind_sc_reply` and `sched_context_donate`: the caller's SC
gets the reply on top of its call stack and moves to the callee.
-/
import Fl4Proofs.P3.ScCallPush
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`reply_push`'s donation branch refines `bind_sc_reply` and
`sched_context_donate`**: the caller `f`'s SC `sc` takes the detached,
isolated reply `r` on its stack and moves to the callee `t` (which has no
SC). -/
theorem push_donate_refines {N T C R : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) {f : U64} (hf : f ∈ T) (hyf : y.scTcb = some f.bv)
    {xf : Fl4Spec.Tcb} (hkf : σ.kheap f.bv = some (.tcb xf)) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t.bv = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none) (hft : f ≠ t)
    (hrel : inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)
    {r : U64} (hr : r ∈ R) (hdet : Detached C Lst r) (hiso : Isolated (L.mem s) R r)
    (hRF : RFree (L.mem s) R C σ Lst) (hnf : ¬ Free σ r) :
    (do
      let i2 ← obj.Sc.reply st sc s
      let s3 ← if i2 != 0#u64 then obj.Reply.set_next st i2 s r false else ok s
      let s4 ← obj.Reply.set_prev st r s3 i2
      let s5 ← obj.Sc.set_reply st sc s4 r
      let s6 ← obj.Reply.set_next st r s5 sc true
      schedcontext.donate st ar s6 a sc t) ⦃ res => ∃ σ' Lst',
      (do
        Fl4Spec.bindScReply (Z := Unit) sc.bv r.bv
        Fl4Spec.schedContextDonate (Z := Unit) sc.bv t.bv) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c res.1 σ' ∧ NtfnStateRel N T (L.mem res.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      CallRel (L.mem res.1) R C σ' Lst' ∧ RPlaced st N T C R c res.1 σ' ∧ RFree (L.mem res.1) R C σ' Lst' ⦄ := by
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
      (do
        let s4 ← obj.Reply.set_prev st r s3 ((Lst sc).headD 0#u64)
        let s5 ← obj.Sc.set_reply st sc s4 r
        let s6 ← obj.Reply.set_next st r s5 sc true
        schedcontext.donate st ar s6 a sc t) ⦃ res => ∃ σ' Lst',
        (do
          Fl4Spec.bindScReply (Z := Unit) sc.bv r.bv
          Fl4Spec.schedContextDonate (Z := Unit) sc.bv t.bv) σ = ({((), σ')}, False) ∧
        SchedRel st N T C c res.1 σ' ∧ NtfnStateRel N T (L.mem res.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        CallRel (L.mem res.1) R C σ' Lst' ∧ RPlaced st N T C R c res.1 σ' ∧ RFree (L.mem res.1) R C σ' Lst' ⦄ := by
    intro s3 σA hS3 hR3 hN3 hI3 hks3 hkA hkh3 htm3 hcase hm3 hmH3
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
    have hrelB : inClass xt.tcbState → Fl4Spec.scActive { y with scReplies := r.bv :: y.scReplies } = true →
        released σB { y with scReplies := r.bv :: y.scReplies } := fun h1 h2 => by
      have := hrel h1 h2
      unfold released at this ⊢
      rw [show σB.curTime = σ.curTime from htm3]; exact this
    refine WP.spec_mono (donate_bound_refines s6 a σB hS6 hR6 hNB hIB hsc hsc0 hkscB hf hyf hkfB ht hktB hxt0 hft
      hrelB) ?_
    rintro res ⟨σ', hdon, -, hS', hR', hN', hI', hw', hksc', hko', hkf', hkt', -, -, -⟩
    obtain ⟨cw1, cw2⟩ := callWords_of_dfoot hS6 hRP6 hsc hw'
    have hqC : ∀ q ∈ C, q.bv ≠ f.bv ∧ q.bv ≠ t.bv := fun q hq => by
      obtain ⟨Q, R', hc, hs⟩ := hS.lists
      obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
      exact ⟨fun e => (by rw [e, hkf] at hkq; cases hkq), fun e => (by rw [e, hkt] at hkq; cases hkq)⟩
    refine ⟨σ', Function.update Lst sc (r :: Lst sc), ?_, hS', hR', hN', hI', ?_, ?_, ?_⟩
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
      (Or.inl ⟨hL, rfl⟩) (fun b _ _ => rfl) (fun d hh => by rw [hL] at hh; cases hh)
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

end

end

end Fl4Proofs.P3.Sched
