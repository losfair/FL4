/-
P3 (DESIGN.md §9), IPC: **`handle_fault` with an endpoint fault handler and
no waiting receiver at `J`** (`JAtZ.faultBlockJ`; the waiting receiver is
XTopJointFaultRecv's `JAtZ.faultRecvJ`).

FL4's `faults::handle_fault` with an endpoint cap in the current thread's
fault-handler slot: `send_fault_ipc`'s endpoint branch, `set_fault` (for a
cap fault the lookup-failure words, then the fault words), then a blocking
`send_ipc` (call, the cap's grant rights, `can_donate` from the thread's SC
word); the spec's `handleFault`: `sendFaultIpc` = `threadSet` of the fault,
then `sendIpc` (blocking, call), then `return true`.

* `CapFaultCorr f f'` (defined in IpcGrant, where `lookup_extra_loop`'s
  failure produces it): FL4's fault is a cap fault and the spec's the same
  cap fault, the lookup failures related (`LookupFaultRel`, with its bounds).
* `encode_lfRel`: `LookupFault::encode` of related lookup failures gives the
  words `LfRel` reads (the guard mismatch's packed word by the bounds).
* `set_fault_cap_eq`: the seven words `set_fault` writes for a cap fault.
* `fault_set_ipc7`, `fault_word_sre7`, `fault_word_top7`: IpcTimeout's
  `fault_set_ipc` / `fault_word_sre` / `fault_word_top` over the seven fault
  and lookup-failure words (`[t+3376, t+3432)`); `set_fault_cap_top`:
  `set_fault` of a cap fault refines l4v's `thread_set` of the fault, on
  `IRel`.
* `handleFault_ep_mem`: the spec's outcome from `sendIpc`'s.
* `JAtZ.faultBlockJ`: the whole `handle_fault` at `J` when the handler
  endpoint is idle or sending (XTopJointSendBlockG's `JAtZ.runTmoJ` tail
  for the current thread, with XTopJointSendBlock's `JAtZ.sendBlockJ`'s
  scheduler facts: P1's `CanBlock` of the current runnable thread, the
  pending reschedule after, `Inv.rd` of the now blocked sender carried from
  the runnable thread's `RelIfBound`; a cap fault is no timeout fault, so
  `inClassR` holds for it and `Inv.rd` must hold, and does).
-/
import Fl4Proofs.P3.XTopJointNoFault
import Fl4Proofs.P3.XTopJointSendBlockG
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

/-- A failed cap lookup's fault (`handle_invocation`'s). -/
theorem capFaultCorr_lookup (cptr : U64) {lf : error.LookupFault} {lf' : Fl4Spec.LookupFailure}
    (h : LookupFaultRel lf lf') :
    CapFaultCorr (.Cap cptr false lf) (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) false lf') :=
  ⟨cptr, false, lf, lf', rfl, by rw [ofBl_toBl64], h⟩

/-- **`LookupFault::encode` of related lookup failures** (module docstring). -/
theorem encode_lfRel {lf : error.LookupFault} {lf' : Fl4Spec.LookupFailure} (h : LookupFaultRel lf lf') :
    error.LookupFault.encode lf ⦃ r => LfRel r.1 r.2.1 r.2.2 lf' ⦄ := by
  unfold error.LookupFault.encode
  cases lf <;> cases lf' <;> simp only [LookupFaultRel] at h
  · rw [WP.spec_ok]; rfl
  · rw [WP.spec_ok]; exact ⟨rfl, h.symm⟩
  · rw [WP.spec_ok]; exact ⟨rfl, h.2.symm, h.1.symm⟩
  · rename_i g left gs bl gl
    obtain ⟨h1, h2, hg, hgs, hl⟩ := h
    dsimp only
    rw [shl_eq left 8#i32 (by decide) (by decide)]
    simp only [bind_ok, lift, WP.spec_ok]
    have hsh : (left.bv <<< (8#i32 : I32).toNat).toNat = left.val * 256 := by
      rw [BitVec.toNat_shiftLeft]
      show (left.val <<< 8) % 2 ^ 64 = _
      rw [Nat.shiftLeft_eq]; omega
    have hor : ((⟨left.bv <<< (8#i32 : I32).toNat⟩ : U64) ||| gs).val = left.val * 256 + gs.val := by
      rw [UScalar.val_or]
      show (left.bv <<< (8#i32 : I32).toNat).toNat ||| gs.val = _
      rw [hsh, show left.val * 256 = left.val <<< 8 by rw [Nat.shiftLeft_eq],
        ← Nat.shiftLeft_add_eq_or_of_lt (by omega : gs.val < 2 ^ 8)]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [h2, ofBl_bitsOf_eq, Nat.mod_eq_of_lt hg]; exact BitVec.eq_of_toNat_eq (by simp)
    · rw [hor, h1, Nat.shiftRight_eq_div_pow]; omega
    · rw [hor, h2, length_bitsOf]; omega

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`set_fault` of a cap fault** writes the seven fault and lookup-failure
words. -/
theorem set_fault_cap_eq (s : S) (t a : U64) (rp : Bool) (lf : error.LookupFault) {lt l0 l1 : U64}
    (he : error.LookupFault.encode lf = ok (lt, l0, l1)) :
    faults.set_fault st s t (.Cap a rp lf) ⦃ s' => s' =
      L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1)
        (tFaultA t) fl4_abi.consts.fault.CapFault) (tFw0A t) a) (tFw1A t) (if rp then 1#u64 else 0#u64))
        (tFw2A t) 0#u64 ⦄ := by
  unfold faults.set_fault
  refine WP.spec_bind (Pₘ := fun r : S × U64 × U64 × U64 × U64 =>
      r = (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1, fl4_abi.consts.fault.CapFault, a,
        (if rp then 1#u64 else 0#u64), 0#u64)) ?_ ?_
  · simp only [he, bind_ok]
    refine WP.spec_bind (obj.Tcb.set_lf_type.wr s t lt) fun s2 e2 => ?_
    subst e2
    refine WP.spec_bind (obj.Tcb.set_lf_w0.wr _ t l0) fun s3 e3 => ?_
    subst e3
    refine WP.spec_bind (obj.Tcb.set_lf_w1.wr _ t l1) fun s4 e4 => ?_
    subst e4
    cases rp <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok] <;> rfl
  · rintro ⟨s1, ty, w0, w1, w2⟩ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hh
    try simp only [uncurry_apply_pair]
    step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s2, hs2⟩
    step with set_fault_w0_spec as ⟨s3, hs3⟩
    step with set_fault_w1_spec as ⟨s4, hs4⟩
    refine WP.spec_mono (set_fault_w2_spec s4 t 0#u64) ?_
    rintro s5 rfl
    subst hs2 hs3 hs4
    rfl

end

section Fault
open Fl4Proofs.P3.Sched
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem tf_faultRange7 {t b : U64} (hta : TcbAddr t) (hb : Aligned b) (h1 : t.val + 3376 ≤ b.val)
    (h2 : b.val < t.val + 3432) : TF t b := by
  have := hta.align
  unfold TF TOffN; unfold Aligned at hb; omega

/-- **The fault and lookup-failure words of a TCB rewritten** (from
`t + 3376` to `t + 3432`; IpcTimeout's `fault_set_ipc` over seven words). -/
theorem fault_set_ipc7 (hP0 : IPlaced N T E R B) {s s' : S} {σ : Fl4Spec.State Unit}
    (hR : IpcRel N T E R B (L.mem s) σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (f : Option Fl4Spec.Fault)
    (hag : ∀ w, Aligned w → (w.val < t.val + 3376 ∨ t.val + 3432 ≤ w.val) → L.mem s' w = L.mem s w)
    (h0 : L.mem s' (tFaultA t) = 0#u64 ↔ f = none) (h5 : L.mem s' (tFaultA t) = 5#u64 ↔ ∃ b, f = some (.timeout b))
    (hfr : FaultRel (L.mem s') t f) :
    IpcRel N T E R B (L.mem s') (updK σ t.bv (.tcb { x with tcbFault := f })) := by
  have hta := hP0.e.tcb t ht
  have g : ∀ w, Aligned w → (w.val < t.val + 3376 ∨ t.val + 3432 ≤ w.val) → L.mem s' w = L.mem s w := hag
  obtain ⟨x0, hk0, hx⟩ := hR.tcb t ht
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  refine hR.upd_tcb hP0 ht _ (fun b hb ⟨_, hnt⟩ => g b hb (by
      by_contra hc; push_neg at hc
      exact hnt (Or.inl (tf_faultRange7 hta hb hc.1 hc.2)))) (Or.inr ⟨g _ (a_st hta).1 (by rw [val_st hta]; omega),
      g _ (a_blk hta).1 (by rw [val_blk hta]; omega)⟩) ?_
  have hreg : ∀ r, (regA t (regIdx r)).val < t.val + 3376 := fun r => by
    rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega
  refine ⟨?_, fun e he => ?_, fun n hn => ?_, fun e d h => ?_, fun e r d h => ?_, fun r h => ?_, fun r => ?_,
    ?_, h0, h5, ?_, hfr, ?_⟩
  · rw [g _ (a_st hta).1 (by rw [val_st hta]; omega)]; exact hx.st
  · rw [g _ (a_blk hta).1 (by rw [val_blk hta]; omega)]; exact hx.blkE e he
  · rw [g _ (a_blk hta).1 (by rw [val_blk hta]; omega)]; exact hx.blkN n hn
  · rw [g _ (a_badge hta).1 (by rw [val_badge hta]; omega), g _ (a_flags hta).1 (by rw [val_flags hta]; omega)]
    exact hx.send e d h
  · rw [g _ (a_reply hta).1 (by rw [val_reply hta]; omega)]; exact hx.recv e r d h
  · rw [g _ (a_reply hta).1 (by rw [val_reply hta]; omega)]; exact hx.reply r h
  · rw [g _ (a_reg hta r).1 (Or.inl (hreg r))]; exact hx.regs r
  · rw [g _ (a_prio hta).1 (by rw [val_prio hta]; omega)]; exact hx.prio
  · rw [g _ (a_bound hta).1 (by rw [val_bound hta]; omega)]; exact hx.bound
  · rw [g _ (scA_aligned hta) (by rw [scA_val hta]; omega)]; exact hx.sc

/-- A fault or lookup-failure word offset of a TCB. -/
def FaultOff7 (K : U64) : Prop :=
  K = 3376#u64 ∨ K = 3384#u64 ∨ K = 3392#u64 ∨ K = 3400#u64 ∨ K = 3408#u64 ∨ K = 3416#u64 ∨ K = 3424#u64

theorem FaultOff7.val {K : U64} (h : FaultOff7 K) : 3376 ≤ K.val ∧ K.val < 3432 ∧ K.val % 8 = 0 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The scheduler relation after a write to a fault or lookup-failure
word** (IpcTimeout's `fault_word_sre`). -/
theorem fault_word_sre7 {s : S} {σ : Fl4Spec.State Unit} (hS : SRE st N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (f : Option Fl4Spec.Fault) {K : U64} (hK : FaultOff7 K)
    (v : U64) :
    SRE st N T C E R B c (L.wr s (core.num.U64.wrapping_add t K) v) (updK σ t.bv (.tcb { x with tcbFault := f })) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.1.lists
  have hta := hc.tcbs t ht
  obtain ⟨k1, k2, k3⟩ := hK.val
  have hK' : K.val < 4096 := by omega
  have ha := sagree_tcb_wr hS.1 ht (K := K) hK' k3 (fun K' h => by
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) v
  have hw : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta hK' k3
  have hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      nodeW st (L.wr s (core.num.U64.wrapping_add t K) v) c o = nodeW st s c o := fun o ho h8 => by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [Sched.nodeAt_ksb (st := st) (L.ksb_wr _ _ _)]
    exact rd_wr_ne hw (nodeAt_aligned hc.node ho h8) (Ne.symm (nodeAt_ne_tfield hc.node ho ht hta hK'))
  refine ⟨hS.1.of_sagreeE ha (hn _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    (hn _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])) hS.1.nodeNW hS.1.domNW hS.1.dtNW
    (SchedStep.updK_tcb hk rfl rfl rfl), hS.2.mono (L.ksb_wr _ _ _) (SzKeep.updK hk (fun _ _ h => by cases h))⟩

/-- **`RelTopI ∧ SRE` after a write to a fault or lookup-failure word**
(IpcTimeout's `fault_word_top`). -/
theorem fault_word_top7 {s : S} {σ : Fl4Spec.State Unit} (hS : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (f : Option Fl4Spec.Fault)
    {K : U64} (hK : FaultOff7 K) (v : U64) :
    SRT st th cr N T C E R B c (SRE st N T C E R B c) (L.wr s (core.num.U64.wrapping_add t K) v)
      (updK σ t.bv (.tcb { x with tcbFault := f })) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.2.1.lists
  have hta := hc.tcbs t ht
  obtain ⟨k1, k2, k3⟩ := hK.val
  have hK' : K.val < 4096 := by omega
  have hv := tfield_val hta hK'
  refine ⟨hS.1.frame (writesIn_wr (field_aligned hta hK' k3)) (fun a ha => Or.inl ⟨t, ht, ?_, ?_⟩)
    (fun a ha => by rw [ha]; exact NoBufW.off hc.tcbs ht hK' (by omega)) ?_ rfl rfl
    (VsKeep.updK_tcb hk rfl),
    fault_word_sre7 hS.2 ht hk f hK v⟩
  · rw [ha, hv]; omega
  · rw [ha, hv]; omega
  · refine ⟨fun o => ?_, fun o r cs hc' _ => ?_, fun o y hy => ?_, rfl, rfl⟩
    · by_cases e : o = t.bv
      · subst e
        refine ⟨fun r cs h _ => by simp [updK] at h, fun _ _ => ⟨x, hk⟩, fun hn => by rw [hk] at hn; cases hn⟩
      · simp only [updK, Function.update_of_ne e]
        exact ⟨fun r cs h hw => ⟨cs, h, hw⟩, fun y h => ⟨y, h⟩, id⟩
    · have e : o ≠ t.bv := by rintro rfl; rw [hk] at hc'; cases hc'
      simp only [updK, Function.update_of_ne e]; exact hc'
    · by_cases e : o = t.bv
      · subst e; rw [hk] at hy; cases hy
        exact ⟨{ x with tcbFault := f }, by simp [updK], rfl⟩
      · exact ⟨y, by simp only [updK, Function.update_of_ne e]; exact hy, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **`set_fault` of a cap fault** refines l4v's `thread_set` of the fault,
on `IRel` (module docstring). -/
theorem set_fault_cap_top (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    {f : error.Fault} {f' : Fl4Spec.Fault} (hf : CapFaultCorr f f') :
    faults.set_fault st s t f ⦃ s' =>
      Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some f' }) t.bv σ =
        ({((), updK σ t.bv (.tcb { x with tcbFault := some f' }))}, False) ∧
      IRel st th cr N T C E R B c s' (updK σ t.bv (.tcb { x with tcbFault := some f' })) ⦄ := by
  obtain ⟨a, rp, lf, lf', rfl, rfl, hlf⟩ := hf
  obtain ⟨⟨lt, l0, l1⟩, he, hlr⟩ := spec_exists (encode_lfRel hlf)
  obtain ⟨hIR, hSRT⟩ := hX
  have hta := hP0.e.tcb t ht
  set fo : Option Fl4Spec.Fault := some (.capFault a.bv rp lf')
  set y : Fl4Spec.Tcb := { x with tcbFault := fo }
  set σ' := updK σ t.bv (.tcb y)
  have hk' : σ'.kheap t.bv = some (.tcb y) := by simp [σ']
  have hidem : updK σ' t.bv (.tcb { y with tcbFault := fo }) = σ' := by
    show updK (updK σ t.bv (.tcb y)) t.bv (.tcb y) = _; rw [updK_idem']
  refine WP.spec_mono (set_fault_cap_eq (L := L) s t a rp lf he) ?_
  rintro s' rfl
  refine ⟨Notif.threadSet_eq _ hk, ?_, ?_⟩
  · -- the IPC relation
    have hla := (a_lf hta).1
    have hl0a := (a_lf0 hta).1
    have hl1a := (a_lf1 hta).1
    have hfa := (a_fault hta).1
    have h0a := (a_fw0 hta).1
    have h1a := (a_fw1 hta).1
    have h2a := (a_fw2 hta).1
    have vl := val_lf hta
    have vl0 := val_lf0 hta
    have vl1 := val_lf1 hta
    have vf := val_fault hta
    have v0 := val_fw0 hta
    have v1 := val_fw1 hta
    have v2 := val_fw2 hta
    have ne : ∀ p q : U64, p.val ≠ q.val → p ≠ q := fun p q h e => h (congrArg UScalar.val e)
    have hag : ∀ w, Aligned w → (w.val < t.val + 3376 ∨ t.val + 3432 ≤ w.val) →
        L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1)
          (tFaultA t) fl4_abi.consts.fault.CapFault) (tFw0A t) a) (tFw1A t) (if rp then 1#u64 else 0#u64)) (tFw2A t) 0#u64) w =
        L.mem s w := by
      intro w hw hr
      rw [rd_wr_ne h2a hw (ne _ _ (by omega)), rd_wr_ne h1a hw (ne _ _ (by omega)),
        rd_wr_ne h0a hw (ne _ _ (by omega)), rd_wr_ne hfa hw (ne _ _ (by omega)),
        rd_wr_ne hl1a hw (ne _ _ (by omega)), rd_wr_ne hl0a hw (ne _ _ (by omega)),
        rd_wr_ne hla hw (ne _ _ (by omega))]
    have rft : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1)
          (tFaultA t) fl4_abi.consts.fault.CapFault) (tFw0A t) a) (tFw1A t) (if rp then 1#u64 else 0#u64)) (tFw2A t) 0#u64)
          (tFaultA t) = 1#u64 := by
      rw [rd_wr_ne h2a hfa (ne _ _ (by omega)), rd_wr_ne h1a hfa (ne _ _ (by omega)),
        rd_wr_ne h0a hfa (ne _ _ (by omega)), rd_wr_eq hfa]
      unfold fl4_abi.consts.fault.CapFault; rfl
    have rf0 : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1)
          (tFaultA t) fl4_abi.consts.fault.CapFault) (tFw0A t) a) (tFw1A t) (if rp then 1#u64 else 0#u64)) (tFw2A t) 0#u64)
          (tFw0A t) = a := by
      rw [rd_wr_ne h2a h0a (ne _ _ (by omega)), rd_wr_ne h1a h0a (ne _ _ (by omega)), rd_wr_eq h0a]
    have rf1 : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1)
          (tFaultA t) fl4_abi.consts.fault.CapFault) (tFw0A t) a) (tFw1A t) (if rp then 1#u64 else 0#u64)) (tFw2A t) 0#u64)
          (tFw1A t) = (if rp then 1#u64 else 0#u64) := by
      rw [rd_wr_ne h2a h1a (ne _ _ (by omega)), rd_wr_eq h1a]
    have rlt : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1)
          (tFaultA t) fl4_abi.consts.fault.CapFault) (tFw0A t) a) (tFw1A t) (if rp then 1#u64 else 0#u64)) (tFw2A t) 0#u64)
          (tLfA t) = lt := by
      rw [rd_wr_ne h2a hla (ne _ _ (by omega)), rd_wr_ne h1a hla (ne _ _ (by omega)),
        rd_wr_ne h0a hla (ne _ _ (by omega)), rd_wr_ne hfa hla (ne _ _ (by omega)),
        rd_wr_ne hl1a hla (ne _ _ (by omega)), rd_wr_ne hl0a hla (ne _ _ (by omega)), rd_wr_eq hla]
    have rl0 : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1)
          (tFaultA t) fl4_abi.consts.fault.CapFault) (tFw0A t) a) (tFw1A t) (if rp then 1#u64 else 0#u64)) (tFw2A t) 0#u64)
          (tLf0A t) = l0 := by
      rw [rd_wr_ne h2a hl0a (ne _ _ (by omega)), rd_wr_ne h1a hl0a (ne _ _ (by omega)),
        rd_wr_ne h0a hl0a (ne _ _ (by omega)), rd_wr_ne hfa hl0a (ne _ _ (by omega)),
        rd_wr_ne hl1a hl0a (ne _ _ (by omega)), rd_wr_eq hl0a]
    have rl1 : L.mem (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr (L.wr s (tLfA t) lt) (tLf0A t) l0) (tLf1A t) l1)
          (tFaultA t) fl4_abi.consts.fault.CapFault) (tFw0A t) a) (tFw1A t) (if rp then 1#u64 else 0#u64)) (tFw2A t) 0#u64)
          (tLf1A t) = l1 := by
      rw [rd_wr_ne h2a hl1a (ne _ _ (by omega)), rd_wr_ne h1a hl1a (ne _ _ (by omega)),
        rd_wr_ne h0a hl1a (ne _ _ (by omega)), rd_wr_ne hfa hl1a (ne _ _ (by omega)), rd_wr_eq hl1a]
    refine fault_set_ipc7 hP0 hIR ht hk fo hag ⟨fun h => absurd (rft.symm.trans h) (by decide), fun h => by
      simp [fo] at h⟩ ⟨fun h => absurd (rft.symm.trans h) (by decide), fun ⟨b, hb⟩ => by simp [fo] at hb⟩ ?_
    show FaultRel' _ _ _ _ _ _ _ fo
    rw [rft, rf0, rf1, rlt, rl0, rl1]
    exact ⟨rfl, rfl, rfl, hlr⟩
  · -- the scheduler and top relations
    have e1 := fault_word_top7 hSRT ht hk fo (K := 3408#u64) (by unfold FaultOff7; decide) lt
    have e2 := fault_word_top7 e1 ht hk' fo (K := 3416#u64) (by unfold FaultOff7; decide) l0
    rw [hidem] at e2
    have e3 := fault_word_top7 e2 ht hk' fo (K := 3424#u64) (by unfold FaultOff7; decide) l1
    rw [hidem] at e3
    have e4 := fault_word_top7 e3 ht hk' fo (K := 3376#u64) (by unfold FaultOff7; decide)
      fl4_abi.consts.fault.CapFault
    rw [hidem] at e4
    have e5 := fault_word_top7 e4 ht hk' fo (K := 3384#u64) (by unfold FaultOff7; decide) a
    rw [hidem] at e5
    have e6 := fault_word_top7 e5 ht hk' fo (K := 3392#u64) (by unfold FaultOff7; decide)
      (if rp then 1#u64 else 0#u64)
    rw [hidem] at e6
    have e7 := fault_word_top7 e6 ht hk' fo (K := 3400#u64) (by unfold FaultOff7; decide) 0#u64
    rw [hidem] at e7
    exact e7

end Fault

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

noncomputable section

section Spec
open Fl4Spec

/-- **l4v `handle_fault` with an endpoint fault handler**: the outcome of
`sendIpc` after the fault is set. -/
theorem handleFault_ep_mem {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {p bd : Word} {r : CapRights} (hc : x.tcbFaultHandler = .endpointCap p bd r) (ex : Fault)
    {z : Unit × State Unit}
    (hz : z ∈ (sendIpc (Z := Unit) true false bd (decide (Rights.allowGrant ∈ r)) (decide (Rights.allowGrantReply ∈ r))
      (decide (x.tcbSchedContext ≠ none)) t p (Notif.updK σ t (.tcb { x with tcbFault := some ex }))).1) :
    ((), z.2) ∈ (handleFault (Z := Unit) t ex σ).1 := by
  unfold handleFault getTcbFaultHandlerPtr
  rw [nd_pure_bind', nd_bind_one (getCap_tcb_three hk), hc, nd_bind_one (threadGet_eq _ hk)]
  unfold sendFaultIpc
  dsimp only
  rw [nd_bind_assoc_fun, nd_bind_one (Notif.threadSet_eq _ hk)]
  refine mem_bind_nd (x := (true, z.2)) ?_ ?_
  · refine mem_bind_nd (x := z) hz ?_
    simp [pure, NonDet.pure]
  · simp [pure, NonDet.pure, NonDet.unless]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 64000000 in
/-- **`handle_fault` with an endpoint handler and no waiting receiver at
`J`** (module docstring). -/
theorem JAtZ.faultBlockJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {ptr bdg : U64} {sd rv g gr : Bool}
    (hep : capAt (L.mem s) (cslotAddr (ct.bv, Fl4Spec.tcbCnodeIndex 3)) = ok (.Endpoint ptr bdg sd rv g gr))
    (hcb : ∀ xe, σ.kheap ptr.bv = some (.endpoint xe) → Endp.CanBlock false xe)
    {f : error.Fault} {f' : Fl4Spec.Fault} (hf : CapFaultCorr f f') :
    faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨a0, rp, lf, lf', rfl, rfl, hlf⟩ := hf
  obtain ⟨⟨lt, l0, l1⟩, he, -⟩ := spec_exists (encode_lfRel hlf)
  obtain ⟨hcur, x, hk, hrn⟩ := J.curRunnable hni hct
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hcq.cur] at h; exact h
  have ht : ct ∈ Z.T := by rw [hct']; exact hcq.curT
  have hta := hP0.e.tcb ct ht
  have htH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct ht
  have htD : ct ∉ D := fun h => J.notDead ht hk (by have := runnable_code hrn; omega) ct h rfl
  have hnq' : ∀ d p, ct.bv ∉ σ.readyQueues d p := by rw [← hcur]; exact hnq
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  have hnr : ct.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  have hidt : σ.idleThread ≠ ct.bv := fun e => hti (by rw [hcur, e])
  -- the handler cap, its endpoint
  obtain ⟨x1, c1, hk1, hc1, hcr⟩ := fhCap_rel J.xtop.rel.2.1.1 htcb
  rw [hk] at hk1; cases hk1
  have e1 : c1 = .Endpoint ptr bdg sd rv g gr := by rw [hep] at hc1; simpa using hc1.symm
  subst e1
  have habs := hcr.2
  simp only [absCap] at habs
  have hfh : x.tcbFaultHandler = .endpointCap ptr.bv bdg.bv (rightsOf sd rv g gr) := habs.symm
  have hAS : AbsSlot Z.th (ct.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨ct, rfl, Or.inr ⟨htcb, 3, by decide, rfl⟩⟩
  have hpE : ptr ∈ Z.E := J.slotE hAS hep
  obtain ⟨xe, hke, -⟩ := hI.1.ep ptr hpE
  have hcbe : Endp.CanBlock false xe := hcb xe hke
  have hpt : ptr.bv ≠ ct.bv := fun e => by rw [e, hk] at hke; cases hke
  have hHe : H ptr = some .ep := J.zH.2.1 ptr hpE
  have hfit := J.kern.heap.fits ptr _ hHe
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap (P1.WritesIn.refl s _) hAS.isSlot hep (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_ep ptr bdg sd rv g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  -- P1's `CanBlock` of the current thread
  obtain ⟨bq, br⟩ := J.curBits ht hnq' hnr
  obtain ⟨hna, -⟩ := J.words_of_spec ht (fun u hu => by rw [hni.2] at hu; cases hu)
    (fun e => hni.1 (by rw [hcur, e]))
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb ct ht
  rw [hk] at hk0; cases hk0
  have hv : (L.mem s (P1.stA ct)).val = tsCode x.tcbState := by
    rw [P1.stA_eq, ← tStA_eq]; exact hTR.st
  obtain ⟨hnb, hnrp⟩ := P1.run_word (w := L.mem s (P1.stA ct)) (by rw [hv]; exact runnable_code hrn)
  have ha0 : L.actionW s = 0#u64 := by
    have h := hS.act
    rw [hni.2] at h
    unfold P1.LawfulStore.actionW; rw [hcq.cur]; exact h
  have hcw : L.curW s = ct := by
    apply P1.eq_of_bv
    rw [← hcur, hs.curThread]
    unfold P1.LawfulStore.curW nodeW; rw [hcq.cur]
  have hcbP : P1.CanBlock st (P1.Heap.tcbs H) Ac s ct := by
    obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
    refine ⟨htH, hnb, hnrp, bq, br, hna, ?_, ?_⟩
    · intro h
      have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
        unfold P1.LawfulStore.idleW nodeW; rw [hcq.cur]
      exact hti (by rw [hcur, hs.idleTh, ← ei, h])
    · exact fun h1 => hB0.sact ct htH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hcw⟩))))) h1
  -- the spec's donation flag is FL4's
  obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs.tcb ct ht
  rw [hk] at hkt6; cases hkt6
  have hdon : (L.mem s (scA ct) != 0#u64) = decide (x.tcbSchedContext ≠ none) := by
    rw [hsct6]
    by_cases h0 : L.mem s (scA ct) = 0#u64
    · simp [h0, Notif.optRef]
    · simp [h0, Notif.optRef]
  -- `handle_fault`: the handler cap
  unfold faults.handle_fault
  rw [tcb_slot_fault]
  apply ok_bind_spec
  rw [slot_cap_eq, hep]
  apply ok_bind_spec
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => r.1 = true ∧
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault a0.bv rp lf') σ).1,
      RelTopM (L := L) r.2.1 z.2 ∧ JAt (L := L) arI AR r.2.1 r.2.2 z.2) ?_ ?_
  swap
  · rintro ⟨b0, s2, a2⟩ ⟨hb, hr0⟩
    simp only at hb hr0
    subst hb
    exact (WP.spec_ok _).2 hr0
  unfold faults.send_fault_ipc
  dsimp only
  -- `set_fault`
  set f' : Fl4Spec.Fault := .capFault a0.bv rp lf' with hf'
  set x2 : Fl4Spec.Tcb := { x with tcbFault := some f' } with hx2
  set σf := updK σ ct.bv (.tcb x2) with hσf
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_fault_cap_top hP0 hI ht hk ⟨a0, rp, lf, lf', rfl, rfl, hlf⟩)
      (set_fault_cap_eq (L := L) s ct a0 rp lf he))
      (WP.spec_and (P1.faults.set_fault.blk (U := ∅) s ct (.Cap a0 rp lf) (t0 := ct) J.blk htH
        (fun _ h => by simp at h) hcbP)
        (P1.faults.set_fault.kw (Cs := Cs) (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
          (Es := P1.EH H) s ct (.Cap a0 rp lf) hTH htH))) ?_
  rintro s7 ⟨⟨⟨-, hI7⟩, hs7⟩, ⟨hblk7, -, hcb7⟩, hfoot7⟩
  have hkf : σf.kheap ct.bv = some (.tcb x2) := by simp [hσf, updK]
  have hkfp : ∀ q, q ≠ ct.bv → σf.kheap q = σ.kheap q := by
    intro q hq'; rw [hσf]; simp only [updK, Function.update_of_ne hq']
  have hkef : σf.kheap ptr.bv = some (.endpoint xe) := by rw [hkfp _ hpt]; exact hke
  -- the FL4 step of `set_fault`: the seven words
  have hC2 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ s7 σf := by
    refine ⟨?_, SzKeepC.of (SzKeep.of_tcb (p := ct.bv) (x' := x2) (fun q hq' => by simp [hσf, updK, hq']) hkf)⟩
    subst hs7
    have w := ((((((writesIn_wr (st := st) (s := s) (v := lt) (a_lf hta).1).trans
      (writesIn_wr (v := l0) (a_lf0 hta).1)).trans (writesIn_wr (v := l1) (a_lf1 hta).1)).trans
      (writesIn_wr (v := fl4_abi.consts.fault.CapFault) (a_fault hta).1)).trans (writesIn_wr (v := a0) (a_fw0 hta).1)).trans
      (writesIn_wr (v := if rp then 1#u64 else 0#u64) (a_fw1 hta).1)).trans
      (writesIn_wr (v := 0#u64) (a_fw2 hta).1)
    refine w.mono fun w0 hw0 => ?_
    have k : ∃ K : Nat, 256 ≤ K ∧ K < 4096 ∧ K ≠ 3440 ∧ K ≠ 3472 ∧ (K ≠ 3512 ∧ K ≠ 3664) ∧ w0.val = ct.val + K := by
      rcases hw0 with ((((((h | h) | h) | h) | h) | h) | h) <;> subst h
      · exact ⟨3408, by omega, by omega, by omega, by omega, by omega, val_lf hta⟩
      · exact ⟨3416, by omega, by omega, by omega, by omega, by omega, val_lf0 hta⟩
      · exact ⟨3424, by omega, by omega, by omega, by omega, by omega, val_lf1 hta⟩
      · exact ⟨3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩
      · exact ⟨3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩
      · exact ⟨3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩
      · exact ⟨3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩
    obtain ⟨K, k1, k2, k3, k4, k5, k6⟩ := k
    exact Or.inl (Or.inr ⟨ct, ht, K, k1, k2, k3, k4, k5, k6⟩)
  -- the spec's blocking send at `σf`
  have hprf : ∀ u, Sched.prioOf σf u = Sched.prioOf σ u := by
    intro u
    by_cases hut : u = ct.bv
    · subst hut; exact (prioOf_eq hkf).trans (prioOf_eq hk).symm
    · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq, hkfp u hut]
  have hnb0 : tsCode x.tcbState ≠ 3 ∧ tsCode x.tcbState ≠ 4 := by
    have := runnable_code hrn; omega
  have htq : ct.bv ∉ xe.epQueue := Endp.not_queued hI.1.toE ht hk hnb0 ptr hpE xe hke
  have hqm : ∀ u ∈ xe.epQueue, ∃ z, σf.kheap u = some (.tcb z) := fun u hu => by
    obtain ⟨z, hz, -⟩ := (J.sv.epQ _ _ hke).2 u hu
    exact ⟨z, by rw [hkfp u (fun e => htq (e ▸ hu))]; exact hz⟩
  obtain ⟨σ', heq, F0, hik0, ⟨ds, hkt'⟩, -, -, hcn, hsrt⟩ :=
    sendIpcBlock_eq hkf hkef hcbe htq hqm hrn ((J.isorted.1 _ _ hke).congr fun u _ => hprf u)
      false bdg.bv g gr (L.mem s (scA ct) != 0#u64)
  -- FL4's blocking send
  have hIS : IpcSorted σf := QPK.QPS.sorted (QPK.qps_upd (ko := .tcb x2) hk rfl) J.isorted
  obtain ⟨⟨Q0, R0, h0⟩, hB0', hX0, hS0, hSg0⟩ := hblk7
  have hst0 : L.epState s7 ptr = 0#u64 ∨ L.epState s7 ptr = 1#u64 := by
    have hx := hI7.1.toE.at_ep hpE hkef
    rw [epState_eq]
    cases xe with
    | idleEP => exact Or.inl hx.1
    | sendEP q => exact Or.inr hx.1
    | recvEP q => simp [Endp.CanBlock] at hcbe
  have hnn : ∀ m, x2.tcbState ≠ .blockedOnNotification m := fun m h => by
    have h' : tsCode x.tcbState = 6 := congrArg tsCode h
    have := runnable_code hrn; omega
  have p1f : endpoint.send_ipc st arI s7 a true false bdg g gr (L.mem s (scA ct) != 0#u64) ct ptr ⦃ s' _ =>
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s7 s' ⦄ :=
    P1.endpoint.send_ipc.blockFoot arI s7 a true false bdg g gr _ ct ptr h0 (fun _ => hcb7) hHe hst0
  refine WP.spec_bind (WP.spec_and (WP.spec_and (send_ipc_blockF (ar := arI) hP0 s7 a σf hI7 ht hkf hnb0 hnn hpE hkef
    hcbe (Sched.qSorted_of_spec (L := L) hI7.1.toE hI7.1.toN hT hIS ptr (Or.inl hpE)) false bdg g gr
    (L.mem s (scA ct) != 0#u64))
    (P1.endpoint.send_ipc.block arI s7 a true false bdg g gr _ ct ptr Q0 R0 h0 hB0' hX0 hS0 hSg0
      (fun _ => hcb7) hHe hst0))
    p1f) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨ea, σ0, h0eq, hIR, hW3⟩, hbk⟩, hfoot3⟩
  simp only [WP.uncurry'_pair] at ea hbk hfoot3 hIR hW3
  subst a'
  obtain rfl : σ' = σ0 := by
    have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
    exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
  apply (WP.spec_ok _).2
  refine ⟨rfl, ?_⟩
  -- the spec's outcome
  have hz : ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv
      (decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr))
      (decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr)) (decide (x.tcbSchedContext ≠ none)) ct.bv
      ptr.bv (updK σ ct.bv (.tcb { x with tcbFault := some f' }))).1 := by
    rw [rights_grant, rights_grantReply, ← hdon]
    show ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr _ ct.bv ptr.bv σf).1
    rw [heq]; exact Set.mem_singleton _
  refine ⟨((), σ'), handleFault_ep_mem hk hfh _ hz, ?_⟩
  -- the frame from the start
  have hkt3 : σ'.kheap ct.bv =
      some (.tcb { x with tcbState := .blockedOnSend ptr.bv ds, tcbFault := some f' }) := hkt'
  have hsk : Sk σ σ' := by
    have h2 : Sk σ σf := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact h2.trans F0.sk
  have F : BFrT ct.bv ptr.bv σ σ' := by
    refine ⟨hsk, fun q => ?_⟩
    by_cases hqt : q = ct.bv
    · subst hqt
      exact Or.inr ⟨_, _, hk, hkt3, Or.inl ⟨x, ptr.bv, ds, some f', rfl, rfl, rfl⟩⟩
    · rcases F0.kh q with e | ⟨o, o', h1, h2, hc⟩
      · exact Or.inl (e.trans (hkfp q hqt))
      · rw [hkfp q hqt] at h1
        rcases hc with ⟨_, _, _, _, _, e3, -⟩ | ⟨x1, y1, rfl, rfl, e3⟩
        · exact absurd e3 hqt
        · exact Or.inr ⟨_, _, h1, h2, Or.inr ⟨x1, y1, rfl, rfl, e3⟩⟩
  -- the FL4 footprint from the start
  have hC3 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf s' σ' := ⟨hW3, SzKeepC.of F0.szKeep⟩
  have hW : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := (hC2.trans hC3).1
  have hfoot := P1.Foot.trans hfoot7 hfoot3
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := ⟨⟨Q0, R0, hbk.1⟩, hbk.2⟩
  -- the assembly (as XTopJointSendBlockG's `JAtZ.runTmoJ`)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hW fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hW
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB hy, hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  -- the scheduler: the current thread blocked, a reschedule pending
  have hcn' : σ'.schedulerAction = .chooseNewThread := hcn hcur.symm hni.2
  have hAI3 : ActIdle σ' := ⟨fun u hu => (by rw [hcn'] at hu; cases hu), F.idleOK J.act.2 hidt⟩
  have hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := Or.inl hcn'
  have hrun3 : CurRunM σ' := Or.inl (by rw [hcn']; intro h; cases h)
  -- the dead: the thread is not dead; the endpoint leaves the dead set
  have hdead : ∀ q ∈ D \ {ptr}, DeadP (L := L) H s' q := fun q hq => by
    have hd := J.jcov.dead q hq.1
    have hqt : q.bv ≠ ct.bv := fun h => htD (by rw [← P1.eq_of_bv h]; exact hq.1)
    have hqe : q.bv ≠ ptr.bv := fun h => hq.2 (P1.eq_of_bv h)
    refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ⟨_, F.tcbO hqt hx, rfl, rfl, Or.inl rfl⟩) (fun x hx => ?_)
      (fun x hx => ⟨x, F.ntfnF hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1
      (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
    obtain ⟨y, hy, hc'⟩ := F.epF hx
    rcases hc' with rfl | e1
    · exact hy
    · exact absurd e1 hqe
  have hidl := J.idleW_keep hS3 F.sk.idle F.sk.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D \ {ptr})
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjcov : JCovD (L := L) Z.th H Z.G (D \ {ptr}) Cs s' := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    exact (J.jcov.undead hcov.1 hcov.2).same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩)
      (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik`; the blocked sender's `RelIfBound` from the runnable thread's)
  have hts6 : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some f' }) ct.bv σ =
      ({((), σf)}, False) := Notif.threadSet_eq _ hk
  have hik : IK ct.bv σ σ' :=
    ((ikm_threadSet (t := ct.bv) (p := ct.bv) (g := fun tcb => { tcb with tcbFault := some f' })
      fun _ => ⟨rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩).of_eq hts6).trans hik0
  have hnqT : NotQueued σ ct.bv := ⟨hnq', hnr⟩
  obtain ⟨hIB, -⟩ := (J.inv.toBut ct.bv).ik hnqT hik
  have hskp : Ipc.SKeep σ σ' := ⟨F.sk.rel, F.sk.tm, fun p y hy => by
    obtain ⟨x', hx', e, -⟩ := F.tcbScB hy; exact ⟨x', hx', e.symm⟩, fun p y n hy => F.scB hy⟩
  have hrib : RelIfBound σ' ct.bv := Ipc.RelIfBound.of_keep (J.inv.rd ct.bv x hk (Or.inl hrn)) hskp
  have I3 : Inv σ' := hIB.inv fun _ _ _ => hrib
  -- `BlockedScActive`: the thread's SC is the current SC, active
  have hscA : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some ct.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp).2⟩
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp hyt
    rw [hk] at hku; cases hku
    obtain ⟨xc, hkc, hcs, -⟩ := hC.tcb
    rw [hcur, hk] at hkc; cases hkc
    have e1 : σ.curSc = q.bv := Option.some.inj (hcs.symm.trans hxs)
    rw [← e1] at hp
    exact hC.active (J.curSc_ne_idle hC hti) y n hp
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {ptr}) s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa hscA, F.isorted J.isorted fun y1 hy1 => (hsrt y1 hy1).congr fun u _ => (hprf u).symm,
      hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have J' := J.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hCs R hKd F.sk.orig hidl.1 (J.zD_diffE hpE)
  exact ⟨⟨_, _, J'.xtop.rel.1, J'.xtop.rel.2.1, J'.xtop.rel.2.2.1, J'.xtop.rel.2.2.2.1, J'.xtop.rel.2.2.2.2.1⟩,
    ⟨_, H, Cs, Ac, Lst, D \ {ptr}, J'⟩⟩

end

end

end Fl4Proofs.P3
