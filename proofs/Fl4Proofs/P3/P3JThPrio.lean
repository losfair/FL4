/-
P3 (p3J gen 40): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at SetPriority (6), for
both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–24 other than 6 / 7 / 14 / 15 / 16 / 18 / 19 /
20 / 21 / 23, or SetEPTRoot}.

* P1 namespace: `dpe_kwN0`, `blocked_kwN0`, `running_kwN0`, **`sched.set_priority.kwN0`** — P1 QueueTcbInv's
  `set_priority` footprint walk (`dpe_kw` / `blocked_kw` / `running_kw` / `sched.set_priority.kw`) at `KWN ∅ False`:
  `sched.dequeue.kwN`, `sched.enqueue.kwN`, `sched.reschedule_required.kwN`, the priority word by `footN_field`, the
  endpoint / notification re-sort by `FootN.of'` + `EpFoot.kwN` / `EpFoot.act` (as P3JCbsFt). Needed because P1's
  `set_priority.kw` is only a `Foot` (`KW`), which allows other cores' node words 8 / 32 that `ProjW` excludes.
* `JAtZ.setPrioProjW` (through `kwN_projW`).
* **`tcb_set_prioJSt`**: XTopJointTcb's `tcb_set_prioJ` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the posts: the restart by `stsProjW`, `set_priority` by `setPrioProjW` beside
  XTopJointTcbPrio's `JAtZ.setPrioJ`).
* **`decThPrioSt`** (any flags): the dispatch leaf (as P3JThMcp's `decThMcpSt`: `XcRel` by `ExtraOK.xc`, `hcapT` from
  the extra cap's slot validity, the arguments by `JAtZ.argsJ`; no premise).
* `ThHard9 l`: `ThHard8 l ∧ l ≠ TCBSetPriority`. `IsRestCap17`. `restCap16_of17`, `restCap17_of`.
  **`midDecRest16_of_prio`** / **`invDecRest16_of_prio`**, `midDecStWL_of_16` / `invDecStWL_of_16`.
* **`DispStabFootLzj` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap17`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzi_of_Lzj`** (under the tops' platform facts), **`dispStabFootLzj_of_Lzi`**; top
  **`kernel_entry_runMcWKR_sysLzj`** (globals verbatim as `_sysLzi`).

Premise honesty: `DispStabFootLzj`'s decode fields are `DispStabFootLzi`'s at the smaller antecedent
(`IsRestCap17 → IsRestCap16`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzj` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThFpuW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {X : Set U64} {Es : Set U64}

theorem dpe_kwN0 (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hnr : ∀ c ∈ Cs, t ∉ R c) (hrun : Runnable (L.mem s (stA t))) :
    (do
      let s1 ← sched.dequeue st s t
      let s2 ← obj.Tcb.set_prio st t s1 prio
      let s3 ← sched.enqueue st s2 t
      sched.reschedule_required st s3) ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
      (h.queued t ht).1)) (sched.dequeue.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t h ht
        (Set.notMem_empty _))) ?_
  rintro s1 ⟨⟨h1, hw1, -⟩, f1⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  obtain ⟨hsb1, -, -⟩ := ext_qfoot h.tcbs hW1 (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw1
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  step with obj.Tcb.set_prio.spec as ⟨s2, s2_post⟩
  subst s2_post
  have f2 : FootN st ∅ False T Cs Sg Scs Z Es s1 (L.wr s1 (prioA t) prio) :=
    footN_field h1.tcbs h1.nodes h1.cur ht (K := 3448#u64) (by simp) (by simp) (by simp) (by simp)
  have h2 := inv_wr_prio h1 ht hq1 hv
  have hr2 : (L.mem (L.wr s1 (prioA t) prio) (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact hnr _ (h2.aff t ht) ((h2.released t ht).1 hcn)
  have hrun2 : Runnable (L.mem (L.wr s1 (prioA t) prio) (stA t)) := by
    rw [(prio_wr_eps (prio := prio) h1 ht).2, (hsb1 t ht).1]
    exact hrun
  refine WP.spec_bind (WP.spec_and (sched.enqueue.inv _ t _ R h2 ht (fun _ => hr2) (fun _ => hrun2))
    (sched.enqueue.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ t h2 ht
      (Set.notMem_empty _))) ?_
  rintro s3 ⟨h3, f3⟩
  exact WP.spec_mono (sched.reschedule_required.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := Es) s3 h3 (fun _ => Set.notMem_empty _))
    fun s' f4 => f1.trans (f2.trans (f3.trans f4))

theorem blocked_kwN0 (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t)))
    (hEs : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → e ∈ Es)
    (reorder : S → U64 → obj.Tcb → Result S)
    (hfoot : ∀ (s : S) (ep : U64) (xs : List U64), TcbPlaced T → EpPlaced T ep →
      QueueRel (L.mem s) T .Ep (L.epQ s ep) xs → t ∈ xs → reorder s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄) :
    (do
      let s1 ← obj.Tcb.set_prio st t s prio
      let i ← obj.Tcb.block_obj st t s1
      reorder s1 i t) ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
  subst s1_post
  have f1 : FootN st ∅ False T Cs Sg Scs Z Es s (L.wr s (prioA t) prio) :=
    footN_field hT h.nodes h.cur ht (K := 3448#u64) (by simp) (by simp) (by simp) (by simp)
  have h1 := inv_wr_prio h ht hq0 hv
  obtain ⟨hbl, hstt⟩ := prio_wr_eps (prio := prio) h ht
  obtain ⟨E, EQ, hEW⟩ := h1.eps
  obtain ⟨heE, htm⟩ := hEW.2.2.2.2.1 t ht htX (by rw [hstt]; exact hb)
  obtain ⟨hE, hEN, hq⟩ := hEW.1 _ heE
  have hEΩ := hEW.2.2.1 _ heE
  have hH : L.mem (L.wr s (prioA t) prio) (blockA t) ∈ Es := hEs _ ((hEW.2.2.2.2.2.2.2.1 _).1 heE)
  step with obj.Tcb.block_obj.spec as ⟨i, i_post⟩
  subst i_post
  exact WP.spec_mono (hfoot _ _ _ h1.tcbs hE hq htm) fun s2 hw =>
    f1.trans (FootN.of' hw (fun b _ hb => EpFoot.kwN h1.tcbs h1.nodes hq.mem hH hE hEN hEΩ (fun h => h.elim) hb)
      (AcK.of_eq (EpFoot.act h1.tcbs h1.nodes h1.cur hq.mem hE hEN hw)))

theorem running_kwN0 (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hrun : Runnable (L.mem s (stA t)))
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    (do
      let b ← sched.queued st s t
      if b = true then do
        let s1 ← sched.dequeue st s t
        let s2 ← obj.Tcb.set_prio st t s1 prio
        let s3 ← sched.enqueue st s2 t
        sched.reschedule_required st s3
      else do
        let t1 ← sched.cur_thread st s
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1
        if b1 = true then do
          let s1 ← sched.dequeue st s t
          let s2 ← obj.Tcb.set_prio st t s1 prio
          let s3 ← sched.enqueue st s2 t
          sched.reschedule_required st s3
        else obj.Tcb.set_prio st t s prio) ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  step with sched.queued.spec as ⟨b, b_post⟩
  split
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    have htq := (h.queued t ht).1 hq1
    exact dpe_kwN0 s t prio Q R h ht hv (fun c hc => h.QR (h.aff t ht) (h.prio t ht) htq hc) hrun
  · step with sched.cur_thread.spec as ⟨t1, t1_post⟩
    step with tcb_eq.blk as ⟨b1, b1_post⟩
    split
    · have e : t = t1 := by simpa [b1_post] using ‹b1 = true›
      have hr0 := hcur (e.trans t1_post)
      exact dpe_kwN0 s t prio Q R h ht hv (fun c hc => h.notR ht hr0 hc) hrun
    · step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
      subst s1_post
      exact footN_field h.tcbs h.nodes h.cur ht (K := 3448#u64) (by simp) (by simp) (by simp) (by simp)


/-- (p3J gen 40) seL4 `setPriority` in `KWN ∅ False` (P1 `sched.set_priority.kw`). -/
theorem sched.set_priority.kwN0 (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.set_priority st s t prio ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := ts_vals
  have hEs : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → e ∈ EH H := fun e he => he
  unfold sched.set_priority
  step with obj.Tcb.state.spec as ⟨sv, sv_post⟩
  subst sv_post
  split
  · exact running_kwN0 s t prio Q R h ht hv (Or.inl ‹_›) hcur
  · split
    · exact running_kwN0 s t prio Q R h ht hv (Or.inr (Or.inl ‹_›)) hcur
    · split
      · exact running_kwN0 s t prio Q R h ht hv (Or.inr (Or.inr ‹_›)) hcur
      · have hnr : ¬ Runnable (L.mem s (stA t)) := by rintro (e | e | e) <;> contradiction
        have hq0 := notQ_of_not_runnable h ht hnr
        have fe := fun (s : S) ep xs hT hE hq hm => endpoint.reorder_ep.foot (st := st) (T := T) s ep t xs hT hE hq hm
        have fn := fun (s : S) ep xs hT hE hq hm =>
          notification.reorder_ntfn.foot (st := st) (T := T) s ep t xs hT hE hq hm
        split
        · exact blocked_kwN0 s t prio Q R h ht hv hq0 (by simp) (Or.inr (Or.inl ‹_›)) hEs _ fe
        · split
          · exact blocked_kwN0 s t prio Q R h ht hv hq0 (by simp) (Or.inl ‹_›) hEs _ fe
          · split
            · exact blocked_kwN0 s t prio Q R h ht hv hq0 (by simp) (Or.inr (Or.inr ‹_›)) hEs _ fn
            · step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
              subst s1_post
              exact footN_field h.tcbs h.nodes h.cur ht (K := 3448#u64) (by simp) (by simp) (by simp) (by simp)


end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 40) **`set_priority` of a thread of `Z.T` writes only `ProjW`** (module docstring). -/
theorem JAtZ.setPrioProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (v : U64) (hv : v.val < 256)
    (hP1 : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (P1.scA t) ≠ 0#u64 ∧ L.mem s (P1.scA t) ∈ Ac) :
    sched.set_priority st s t v ⦃ s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨⟨Q0, R0, h0⟩, -⟩ := J.blk
  exact WP.spec_mono (P1.sched.set_priority.kwN0 (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H)
    (Z := P1.Heap.scBits H) s t v Q0 R0 h0 (J.zH.1 t ht) hv (fun e => (hP1 e).1))
    fun s' f => (P1.WritesA.w f).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **SetPriority at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_set_prioJ`;
module docstring). -/
theorem tcb_set_prioJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBSetPriority p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hX := J.xtop
  have hM := J.mcp
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetPriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_prio_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq, -⟩ := hM q (hcapT h0 q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetPriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, x1, hrc, hst1, hk1, hcur1, e1, hsw1, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
      have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
        have h := stsProjW J (J.thT ct (J.xtop.curTcb (J.curEq hct).1).1) sched.TS_RESTART
        rw [hs1, WP.spec_ok] at h; exact h
      have hlt : y0.val < 256 := by
        have := xq.tcbMcpriority.isLt
        have h2 : ¬ (L.mem s (mcpA q)).val < y0.val := hgt
        omega
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      -- the current thread's invariants after the restart
      have hC1 : Sched.CurInv σ1 := by
        have hC0 := J.curInv (by rw [hni.2]; intro h; cases h)
        have h := hC0.restart (xt := x1) (by rw [hcur1]; exact hk1)
        rw [hcur1] at h
        rw [e1]; exact h
      have hne1 : σ1.curThread ≠ σ1.idleThread := by rw [hct1, hid1]; exact hni.1
      obtain ⟨hc1, hp1⟩ := J1.prioCur hne1 hC1 hpT
      rw [hrc]; simp only [bind_ok, tcs_prio]
      refine WP.spec_bind (WP.spec_and (J1.setPrioJ (fun u h => hsw1 u h) hpT y0 hlt hc1 hp1)
        (J1.setPrioProjW hpT y0 hlt hp1)) ?_
      rintro s2 ⟨⟨σ2, hm2, V2, J2⟩, W2⟩
      refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ2), ?_, ⟨_, _, Or.inl ⟨rfl, rfl⟩,
        J2.xtop.rel.1, J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩,
        ⟨⟨_, _, Ac1, Lst1, D1, J2⟩, W1.projW_trans W2⟩⟩)
      refine invoke_prio_mem ssl _ q.bv blk call don (y := ((), σ2)) ?_
      rw [hm2]; exact Set.mem_singleton _
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _

end

/-- (p3J gen 40) The Thread labels left after SetPriority. -/
def ThHard9 (l : U64) : Prop := ThHard8 l ∧ l ≠ fl4_abi.label.TCBSetPriority

/-- (p3J gen 40) The caps left after the SetPriority leaf, with the message label. -/
def IsRestCap17 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard9 l
  | _, _ => False

theorem restCap16_of17 {cp : capability.Cap} {l : U64} (h : IsRestCap17 cp l) : IsRestCap16 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap17_of {cp : capability.Cap} {l : U64} (h : IsRestCap16 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBSetPriority) : IsRestCap17 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem prio_nonIns : TcbNonIns fl4_abi.label.TCBSetPriority := by
  unfold TcbNonIns fl4_abi.label.TCBSetPriority fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The Thread cap's decode at a dispatch state at SetPriority, any flags** (module docstring). -/
theorem decThPrioSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))} {argsU : List U64}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.Thread p))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hl : info.label = fl4_abi.label.TCBSetPriority) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hPl : Placed Z.th := J.xtop.rel.1
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  have hXc := ExtraOK.xc hPl (hXO e exs he hexs)
  have hcapT : exAt e 0 ≠ 0#u64 → ∀ q, capV (L.mem s') (exAt e 0) = .Thread q → q ∈ (Z.mv Z.G V').T := by
    intro hx q hq
    have h0 := hXc.2 0 (exAt e 0) rfl
    obtain ⟨y, hy⟩ : ∃ y, exs[0]? = some y := by
      rcases exs with _ | ⟨y, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨y, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 y hy
    have hA0 : AbsSlot Z.th y.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hq]))
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSetPriority
  have hl5 : fl4_abi.label.TCBSetPriority.val ≠ 5 ∧ fl4_abi.label.TCBSetPriority.val ≠ 8 ∧
      fl4_abi.label.TCBSetPriority.val ≠ 9 ∧ fl4_abi.label.TCBSetPriority.val ≠ 10 ∧
      fl4_abi.label.TCBSetPriority.val ≠ 11 := by simp [fl4_abi.label.TCBSetPriority]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD prio_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_set_prioJSt s' a' σb J hnib p hpT sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen hArgs
      (J.stallT p hpT) call sl e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) exs hXc hcapT bl don ci buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`MidDecStWL` at `KW ∧ IsRestCap16` from the SetPriority leaf** (module docstring). -/
theorem midDecRest16_of_prio (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetPriority
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThPrioSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap17_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`InvDecStWL` at `KW ∧ IsRestCap16` from the SetPriority leaf** (module docstring). -/
theorem invDecRest16_of_prio (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetPriority
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThPrioSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap17_of hW.2 hS⟩

/-- (p3J gen 40) `MidDecStWL` at `KW ∧ IsRestCap16` gives it at `KW ∧ IsRestCap17` (antitone). -/
theorem midDecStWL_of_16 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap16_of17 hW.2⟩

/-- (p3J gen 40) `InvDecStWL` at `KW ∧ IsRestCap16` gives it at `KW ∧ IsRestCap17` (antitone). -/
theorem invDecStWL_of_16 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap16_of17 hW.2⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 40) **`DispStabFootLzj` [J]**: `DispStabFootLzi` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete and the Thread caps at the TCB invocations (2–24) other than SetPriority /
SetMCPriority / Bind- and UnbindNotification / Set- and UnsetBreakpoint / ConfigureSingleStepping / SetTLSBase /
SetFlags / WriteFPU, or SetEPTRoot (module docstring). -/
structure DispStabFootLzj (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzi.invDecRest` at `KW ∧ IsRestCap17`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzi.midDecRest` at `KW ∧ IsRestCap17`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzi.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzi.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 40) **`DispStabFootLzj → DispStabFootLzi`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzi_of_Lzj (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzj (L := L) arI AR MR s a σ) :
    DispStabFootLzi (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest16_of_prio hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest16_of_prio hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 40) **`DispStabFootLzi → DispStabFootLzj`** (the honesty claim: `DispStabFootLzj` is implied). -/
theorem dispStabFootLzj_of_Lzi {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzi (L := L) arI AR MR s a σ) : DispStabFootLzj (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_16 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_16 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzj` only** (`hLzj` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzj [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzj : DispStabFootLzj (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzi hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzi_of_Lzj hA hnd hM hIp hKD hLzj)

end

end Fl4Proofs.P3.Mc
