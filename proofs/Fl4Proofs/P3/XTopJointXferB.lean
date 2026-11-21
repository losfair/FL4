/-
P3 (DESIGN.md §9), IPC: **the message transfer of `send_ipc` to a waiting
receiver, with or without its receive buffer** (toward XTopJointSendPushD's
`JSendRecvHyp`), on `IRel` inside the dequeued interval (the receiver
blocked but in no queue, so no `JAtZ` state), and the way back to `JAtZ`.

* The transfer frame helpers (moved here from XTopJointSendRecv):
  `epHyps_bufC`, `epBufHyps_bufC`, `epBufMapHyps_bufC`, `bufCover_epStep`,
  `do_ipc_transfer_rg`, `do_ipc_transfer_regsJ` (no receive buffer, any
  grant).
* `RBufW`: the receiver's 128 IPC-buffer words (FL4 addresses).
* `do_ipc_transfer_rgB`: the transfer's FL4 footprint with a receive buffer
  and no cap transferred: the receiver's registers and `RBufW`.
* `do_ipc_transfer_bufE`: EpXferBuf2's `do_ipc_transfer_buf` with the
  spec's outcome as a state (`setUm`, the receiver's TCB changed only in its
  user context), from `EpStep`.
* `mixS`: a state with some words of another (a fold of `L.wr`).
* `JAtZ.bufRebase`: from `JAtZ` at `s` and a later state `s'` whose writes
  from `s` lie in a footprint `F` and the receiver's buffer words, `JAtZ` at
  the virtual state `mixS s s'` (the buffer words written first, each by
  `JAtZ.userWrJ`; the spec changes only user memory), from which `s'` writes
  only in `F` (so the wake-up lemmas `JAtZ.wake_post*` apply there).
* P1 across the buffer words (`blkX_bufw`): the receiver's hole kept by
  writes of words apart from every non-`other` object of `H` (`capw_bx` for
  the words of `Ω`, `xfer_all`'s `UserOK` for the others), split by `mixS`.
* `xferStepJ`: the transfer step of the send-to-receiver lemmas, uniform in
  the receive buffer (no cap transferred: `XferNoCap`).
-/
import Fl4Proofs.P3.XTopJointIpcJ
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-! ## The transfer's frame helpers -/

theorem ipcBufCapOK_epStep {σ σ' : Fl4Spec.State Unit} (h : Endp.IpcBufCapOK σ) (hs : EpStep σ σ') :
    Endp.IpcBufCapOK σ' := by
  intro t x' hx' dev p R mt vms md hf hR
  obtain ⟨-, -, hk⟩ := hs
  have hx : ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbIpcframe = x'.tcbIpcframe ∧ x.tcbIpcBuffer = x'.tcbIpcBuffer := by
    rcases hk t with e | ⟨a, b, h1, h2⟩ | ⟨a, b, h1, h2, -⟩ | ⟨a, b, h1, h2, e⟩
    · exact ⟨x', by rw [← e]; exact hx', rfl, rfl⟩
    · rw [hx'] at h2; cases h2
    · rw [hx'] at h2; cases h2
    · have hb : x' = b := by rw [hx'] at h2; exact Fl4Spec.KernelObject.tcb.inj (Option.some.inj h2)
      subst hb
      exact ⟨a, h1, by rw [e], by rw [e]⟩
  obtain ⟨x, hx, e1, e2⟩ := hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := h t x hx dev p R mt vms md (by rw [e1]; exact hf) hR
  refine ⟨h1, h2, fun k hk' => ?_, by rw [← e2]; exact h4, h5⟩
  obtain ⟨sz, hsz⟩ := h3 k hk'
  rw [← e2]
  refine ⟨sz, ?_⟩
  rcases hk (Endp.bufAddr (p + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k &&&
      ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize sz))) with e | ⟨a, b, h1', -⟩ | ⟨a, b, h1', -, -⟩ | ⟨a, b, h1', -, -⟩
  · rw [e]; exact hsz
  · rw [hsz] at h1'; cases h1'
  · rw [hsz] at h1'; cases h1'
  · rw [hsz] at h1'; cases h1'

theorem ipcBufCapOK_of_kheap {σ σ' : Fl4Spec.State Unit} (h : Endp.IpcBufCapOK σ) (hk : σ'.kheap = σ.kheap) :
    Endp.IpcBufCapOK σ' := by
  intro t x hx dev p R mt vms md hf hR
  obtain ⟨h1, h2, h3, h4, h5⟩ := h t x (by rw [← hk]; exact hx) dev p R mt vms md hf hR
  exact ⟨h1, h2, fun k hk' => by obtain ⟨sz, hsz⟩ := h3 k hk'; exact ⟨sz, by rw [hk]; exact hsz⟩, h4, h5⟩

/-- `EpHyps` with `IpcBufCapOK` carried along (an `EpStep` keeps the TCBs'
buffer fields and the data pages). -/
theorem epHyps_buf {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}
    (hH : EpHyps st T E R B SR) : EpHyps st T E R B (fun s σ => SR s σ ∧ Endp.IpcBufCapOK σ) :=
  ⟨fun s s' σ σ' h hw hs => ⟨hH.stable s s' σ σ' h.1 hw hs, ipcBufCapOK_epStep h.2 hs⟩,
   fun s σ t hR hS ht => WP.spec_mono (hH.scheduleTcb s σ t hR hS.1 ht) fun _ ⟨h1, h2⟩ =>
     ⟨h1, h2, ipcBufCapOK_of_kheap hS.2 (stsAct_kheap σ t.bv)⟩⟩

/-- `EpBufHyps` for `SRS (SRT … SRE)` with `IpcBufCapOK` carried along. -/
theorem epBufHyps_buf {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} :
    EpBufHyps st T E R B (fun s σ => SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ ∧
      Endp.IpcBufCapOK σ) :=
  ⟨fun s σ t x b _ hS _ hk => by
    obtain ⟨⟨G, hB⟩, -⟩ := hS.1.1.1
    exact lookup_buf_rel s σ hB.2.1.1 hB.2.1.2.1 (Ipc.RelTopB.tcbT hB hk) hk hS.2 b⟩

theorem copy_mrs_loop0_rg {T : Set U64} (hT : P1.TcbPlaced T) {s0 s : S} {snd rcv n i : U64} (hr : rcv ∈ T)
    (h : P1.WritesIn st s0 s (XferRegW T ∅)) :
    msg.copy_mrs_loop0 st s snd rcv n i ⦃ r => P1.WritesIn st s0 r.1 (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold msg.copy_mrs_loop0
  apply loop.spec_decr_nat (measure := fun y => 4 - y.2.val)
    (inv := fun y => P1.WritesIn st s0 y.1 (XferRegW T ∅))
  · rintro ⟨s1, i1⟩ h1
    simp only at h1
    dsimp only
    unfold msg.copy_mrs_loop0.body
    split
    · split
      · rename_i _ hi
        have hi' : i1.val < 4 := by simpa [msg.N_MSG_REGISTERS] using hi
        refine WP.spec_bind (msg.msg_register.lt i1) fun rg hrg => ?_
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 rg hS) fun v _ => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.rg (v := v) (s := s1) hT hr hrg) fun s2 w2 => ?_
        step as ⟨i2, hi2⟩
        exact ⟨rg_trans h1 w2, by first | omega | (dsimp only; omega)⟩
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- **`do_ipc_transfer`'s footprint, a receiver without a buffer and a sender
without a fault**: the receiver's registers only. -/
theorem do_ipc_transfer_rg {T : Set U64} (hT : P1.TcbPlaced T) {snd rcv : U64} (hr : rcv ∈ T) (s : S) (a : A)
    (ep badge : U64) (grant : Bool)
    (hb : msg.lookup_ipc_buffer st s true rcv ⦃ w => w = 0#u64 ⦄) (hf : L.mem s (tFaultA snd) = 0#u64) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => P1.WritesIn st s s' (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind hb ?_
  rintro rb rfl
  refine WP.spec_bind (obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  rw [hf, if_pos (by unfold fl4_abi.consts.fault.NullFault; rfl)]
  refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s false snd hS) fun sb _ => ?_
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (P0.msg.msg_info.p0 st s snd hS) fun tag _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun extra _ => ?_
  · split
    · refine WP.spec_bind (P0.ipc.lookup_extra_caps.p0 st s snd sb tag hS) fun r _ => ?_
      rcases r with e | _ <;> exact (WP.spec_ok _).2 trivial
    · exact (WP.spec_ok _).2 trivial
  refine WP.spec_bind (Pₘ := fun r : U64 × S => P1.WritesIn st s r.2 (XferRegW T ∅)) ?_ ?_
  · unfold msg.copy_mrs
    refine WP.spec_bind (copy_mrs_loop0_rg hT hr (P1.WritesIn.refl s _)) ?_
    rintro ⟨s1, i⟩ h1
    first | exact (WP.spec_ok _).2 h1 | (simp only [↓reduceIte, WP.spec_ok]; exact h1) | (simp; exact h1)
  rintro ⟨n, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun r : msginfo.MessageInfo × S => P1.WritesIn st s r.2 (XferRegW T ∅)) ?_ ?_
  · unfold ipc.transfer_caps
    refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun out _ => ?_
    step as ⟨sl0, hsl0⟩
    step as ⟨b, hb0⟩
    split <;> first | exact (WP.spec_ok _).2 h1 | (rw [if_pos rfl]; exact (WP.spec_ok _).2 h1)
  rintro ⟨out2, s2⟩ h2
  simp only at h2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st s s3 (XferRegW T ∅)) ?_
    fun s3 h3 => WP.spec_mono (obj.Tcb.set_reg.rg (s := s3) (v := badge) hT hr
      (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s4 w4 => rg_trans h3 w4
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    WP.spec_mono (obj.Tcb.set_reg.rg (v := w) (s := s2) hT hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => rg_trans h2 w4

/-- `CnW` back to an earlier state with the same kernel base and SC sizes. -/
theorem cnW_back {T N C E R : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit} (hk : L.ksb s' = L.ksb s)
    (hz : SzKeepC C σ σ') {b : U64} (h : CnW (st := st) T N C E R c s' σ' b) : CnW (st := st) T N C E R c s σ b :=
  h.elim (fun h => Or.inl (FinW.back hk hz h)) Or.inr

/-- A thread other than the current one set: no reschedule. -/
theorem stsAct_ne {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} (h : t ≠ σ.curThread) : Notif.stsAct σ t = σ := by
  unfold Notif.stsAct; rw [if_neg (fun h' => h h'.1)]

/-- A bound receive-blocked or inactive thread set `Running`. -/
theorem CFr.stsRun {r t : Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {y : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb y))
    (hrb : RbIn y.tcbState) :
    CFr r t σ (Notif.stsAct (Notif.updK σ t (.tcb { y with tcbState := .running })) t) :=
  (CFr.upd hk (Or.inl ⟨y, .running, y.tcbBoundNotification, y.tcbFault, y.tcbArch, rfl, rfl,
    Or.inr ⟨Or.inl rfl, rfl, hrb, Or.inr (Or.inl rfl)⟩⟩)).trans (CFr.sts _ _ _ _)

/-- `IK t` across an update of `t`'s own TCB keeping its SC. -/
theorem IK.updSelf {t : Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {x y : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x))
    (h1 : y.tcbSchedContext = x.tcbSchedContext) : IK t σ (Notif.updK σ t (.tcb y)) :=
  IK.upd hk ⟨fun x' e => by cases e; exact ⟨y, rfl, h1, fun h => absurd rfl h, fun h => absurd rfl h⟩, fun _ _ e => (by cases e),
    fun _ e => (by cases e), fun _ _ => ⟨x, rfl⟩, fun _ _ e => (by cases e), fun _ e => by cases e⟩

/-- `IK t` across an update of an endpoint or a reply. -/
theorem IK.updOther {t p : Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {o o' : Fl4Spec.KernelObject}
    (hk : σ.kheap p = some o)
    (ho : ∀ o0, o0 = o ∨ o0 = o' → (∀ x, o0 ≠ .tcb x) ∧ (∀ y n, o0 ≠ .schedContext y n) ∧ (∀ x, o0 ≠ .notification x)) :
    IK t σ (Notif.updK σ p o') :=
  IK.upd hk (IKObj.other ho)

theorem IK.sts (t : Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) (u : Fl4Spec.ObjRef) : IK t σ (Notif.stsAct σ u) :=
  IK.of_eq (stsAct_kheap σ u) (by unfold Notif.stsAct; split <;> rfl) (by unfold Notif.stsAct; split <;> rfl)
    (by unfold Notif.stsAct; split <;> rfl)


theorem xferTcb_eqA (xr xs : Fl4Spec.Tcb) (b : Fl4Spec.Badge) :
    xferTcb xr xs b = { xr with tcbArch := (xferTcb xr xs b).tcbArch } := by
  simp only [Endp.xferTcb]; rw [Endp.copyRegsTcb_other]; rfl

/-- `BufCover` across an `EpStep` (the TCBs' buffer fields kept, as
`ipcBufCapOK_epStep`). -/
theorem bufCover_epStep {T : Set U64} {B : Set (U64 × Fl4Spec.Word)} {σ σ' : Fl4Spec.State Unit}
    (h : Endp.BufCover T B σ) (hs : EpStep σ σ') : Endp.BufCover T B σ' := by
  intro t ht x' b p hx' hp w hw
  obtain ⟨-, -, hk⟩ := hs
  have hx : ∃ x, σ.kheap t.bv = some (.tcb x) ∧ Endp.ipcBufOf b x = Endp.ipcBufOf b x' := by
    rcases hk t.bv with e | ⟨x1, y1, h1, h2⟩ | ⟨x1, y1, h1, h2, -⟩ | ⟨x1, y1, h1, h2, e⟩
    · exact ⟨x', by rw [← e]; exact hx', rfl⟩
    · rw [hx'] at h2; cases h2
    · rw [hx'] at h2; cases h2
    · have hb : x' = y1 := by rw [hx'] at h2; exact Fl4Spec.KernelObject.tcb.inj (Option.some.inj h2)
      subst hb
      refine ⟨x1, h1, ?_⟩
      rw [e]; rfl
  obtain ⟨x, hx, e⟩ := hx
  exact h t ht x b p hx (e.trans hp) w hw

/-- `EpHyps` with `IpcBufCapOK` and `BufCover` carried along. -/
theorem epHyps_bufC {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}
    (hH : EpHyps st T E R B SR) (T' : Set U64) :
    EpHyps st T E R B (fun s σ => (SR s σ ∧ Endp.IpcBufCapOK σ) ∧ Endp.BufCover T' B σ) :=
  ⟨fun s s' σ σ' h hw hs => ⟨(epHyps_buf hH).stable s s' σ σ' h.1 hw hs, bufCover_epStep h.2 hs⟩,
   fun s σ t hR hS ht => WP.spec_mono ((epHyps_buf hH).scheduleTcb s σ t hR hS.1 ht) fun _ ⟨h1, h2⟩ =>
     ⟨h1, h2, by unfold Endp.BufCover at *; rw [stsAct_kheap]; exact hS.2⟩⟩

/-- `EpBufHyps` for `SRS (SRT … SRE)` with `IpcBufCapOK` and `BufCover`
carried along. -/
theorem epBufHyps_bufC {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} (T' : Set U64) :
    EpBufHyps st T E R B (fun s σ => (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ ∧
      Endp.IpcBufCapOK σ) ∧ Endp.BufCover T' B σ) :=
  ⟨fun s σ t x b hR hS ht hk => (epBufHyps_buf (st := st)).lookup s σ t x b hR hS.1 ht hk⟩

/-- **`EpBufMapHyps` for `SRS (SRT … SRE)` with `IpcBufCapOK` and
`BufCover` carried along** (IpcBuf's `epBufMapHyps_top`, the two facts from
the state instead of every `SRT` state). -/
theorem epBufMapHyps_bufC {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} (hP0 : Ipc.IPlaced N T E R B) :
    EpBufMapHyps st T E R B (fun s σ => (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ ∧
      Endp.IpcBufCapOK σ) ∧ Endp.BufCover T B σ) := by
  have hbuf : ∀ (σ : Fl4Spec.State Unit) (t : U64) (x : Fl4Spec.Tcb) (b : Bool) (p : Fl4Spec.ObjRef),
      Endp.IpcBufCapOK σ → σ.kheap t.bv = some (.tcb x) → Endp.ipcBufOf b x = some p →
      ∃ pb vms, (∀ k, k < 128 →
          Fl4Spec.inUserFrame (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k) σ) ∧
        pb ≠ 0 ∧
        pb.toNat % 2 ^ Fl4Spec.pageBitsForSize vms = 0 ∧ x.tcbIpcBuffer.toNat % 1024 = 0 ∧
        p = pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms)) := by
    intro σ t x b p hO hk hp
    unfold Endp.ipcBufOf at hp
    split at hp
    · rename_i dev pb R mt vms md he
      split_ifs at hp with hc
      cases hp
      have hro : Fl4Spec.vmReadOnly ⊆ R := by
        rcases hc with h | ⟨h, -⟩
        · exact fun z hz => h (by unfold Fl4Spec.vmReadOnly Fl4Spec.vmReadWrite at *; simp at hz ⊢; simp [hz])
        · exact h
      obtain ⟨-, h0, hd, ha, hpa⟩ := hO t.bv x hk dev pb R mt vms md he hro
      exact ⟨pb, vms, hd, h0, hpa, ha, rfl⟩
    · cases hp
  refine ⟨fun s σ t x b p _ hS ht hk hp => ?_, fun s σ t x p _ hS _ hk hp k hk128 => ?_,
    fun s σ t x p hR hS ht hk hp => ?_⟩
  · obtain ⟨⟨G, hB⟩, -⟩ := hS.1.1.1.1
    refine WP.spec_mono (lookup_buf_full s σ hB.2.1.1 hB.2.1.2.1 (Ipc.RelTopB.tcbT hB hk) hk hS.1.2 b) ?_
    rintro w ⟨h0, hw⟩
    obtain ⟨x', hk', hwx⟩ := hS.1.1.1.1.2.bw t ht
    rw [hk] at hk'; cases hk'
    have hwp := hw hwx p hp
    exact ⟨fun e => (by have h := h0.1 e; rw [hp] at h; cases h), hS.2 t ht x b p hk hp w hwp⟩
  · obtain ⟨pb, vms, hd, -, hpa, ha, rfl⟩ := hbuf σ t x true p hS.1.2 hk hp
    exact hd k hk128
  · obtain ⟨⟨G, hB⟩, -⟩ := hS.1.1.1.1
    obtain ⟨pb, vms, hd, h0, hpa, ha, hpe⟩ := hbuf σ t x true p hS.1.2 hk hp
    have hp0 : (⟨p⟩ : U64) ≠ 0#u64 := by
      intro e
      have e' : p = 0 := congrArg UScalar.bv e
      have hb := Endp.pageBits_mem vms
      have := Endp.buf_frame_base vms pb x.tcbIpcBuffer 0 (by norm_num) hpa ha
      rw [← hpe] at this
      unfold Endp.bufAddr at this
      rw [e'] at this
      simp at this
      exact h0 this.symm
    have hm := hS.2 t ht x true p hk hp ⟨p⟩ rfl
    obtain ⟨dest, slots, heq, -⟩ := WP.spec_exists (Ipc.get_receive_slot_top hP0 hB hR (Ipc.RelTopB.tcbT hB hk) hm hp0 []
      (Aeneas.Std.Array.repeat 3#usize 0#u64))
    exact ⟨slots, heq⟩

/-- **`do_ipc_transfer` without a receive buffer, any grant**, on
`SRN (SRS (SRT … SRE))` with `IpcBufCapOK` and `BufCover` at the state
(IpcGrantX's `do_ipc_transfer_regsT` without `IpcSchedHyps` and the global
`EpBufMapHyps`: `do_ipc_transfer_regsX` on `epBufMapHyps_bufC`, the extra
caps looked up read-only by `lookup_extra_top`). -/
theorem do_ipc_transfer_regsJ {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} {c : U64} (hP0 : Ipc.IPlaced N T E R B) (hP : EPlaced T E R B)
    (hHE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover T B σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : Endp.ipcBufOf true xr = none) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), Notif.updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)))}, False) ∧
      EpStateRel T E R B (L.mem s') (Notif.updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s'
        (Notif.updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
        Endp.IpcBufCapOK (Notif.updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)))) ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b) ⦄ := by
  have hIR := (IpcRel.ofSRN hR hSR).1
  obtain ⟨⟨⟨G, hB⟩, -⟩, -⟩ := hSR.1.1
  refine WP.spec_mono (do_ipc_transfer_regsX (ar := arI) (epHyps_bufC hHE T) (epBufHyps_bufC T)
    (epBufMapHyps_bufC hP0) hP s a σ hR ⟨⟨hSR.1, hOK⟩, hBC⟩ hs hr hne hks hkr hf hrb ep badge grant ?_)
    fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3.1, h4⟩
  intro _ sb tag hsb hext
  have hsb' : sb = 0#u64 ↔ Endp.ipcBufOf false xs = none := by
    rcases hsb with ⟨h1, h2⟩ | ⟨sp, h1, h2, -⟩
    · exact ⟨fun _ => h1, fun _ => h2⟩
    · rw [h1]; exact ⟨fun h => absurd h h2, fun h => by cases h⟩
  have hsm : ∀ sp, Endp.ipcBufOf false xs = some sp → BufMap B sb sp := by
    intro sp h
    rcases hsb with ⟨h1, -⟩ | ⟨sp', h1, -, h3⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h; exact h3
  refine WP.spec_mono (lookup_extra_top hP0 hB hIR (hB.tcbT hks) sb (Endp.ipcBufOf false xs) hsb' hsm tag
    (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register))
    (by show tag.extra_caps.bv.toNat = _; rw [hext]) (by show tag.extra_caps.bv.toNat ≤ 3; rw [hext]; exact extra_le3 _))
    fun _ ⟨l, hl, _⟩ => ⟨l, hl⟩


/-! ## The receiver's buffer words and the transfer's footprint with them -/

/-- The 128 IPC-buffer words at FL4 address `rw`. -/
def RBufW (rw b : U64) : Prop := ∃ i : U64, i.val < 128 ∧ b = Endp.fl4BufA rw i

/-- `RBufW` as a list. -/
def rbList (rw : U64) : List U64 := (List.range 128).map fun k => Endp.fl4BufA rw ⟨BitVec.ofNat 64 k⟩

theorem mem_rbList {rw b : U64} : b ∈ rbList rw ↔ RBufW rw b := by
  unfold rbList RBufW
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨BitVec.ofNat 64 k⟩, ?_, rfl⟩
    show (BitVec.ofNat 64 k).toNat < 128
    rw [BitVec.toNat_ofNat]; omega
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i.val, hi, ?_⟩
    have e : (⟨BitVec.ofNat 64 i.val⟩ : U64) = i := UScalar.eq_of_val_eq (by
      show (BitVec.ofNat 64 i.val).toNat = i.val
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := i.bv.isLt; exact this))
    rw [e]

/-- The transfer's footprint with a receive buffer at `rw`: the receiver's
registers and buffer words. -/
def XferBW (T : Set U64) (rw b : U64) : Prop := XferRegW T ∅ b ∨ RBufW rw b

/-- `copy_mrs`' second loop writes only words of the receive buffer. -/
theorem copy_mrs_loop1_rb {rw : U64} (hal : ∀ i : U64, i.val < 128 → P1.Aligned (Endp.fl4BufA rw i))
    {Wf : U64 → Prop} (hW : ∀ b, RBufW rw b → Wf b) {s0 : S} (s : S) (h : P1.WritesIn st s0 s Wf) (sw n i0 : U64) :
    msg.copy_mrs_loop1 st s sw rw n i0 ⦃ r => P1.WritesIn st s0 r.2 Wf ⦄ := by
  unfold msg.copy_mrs_loop1
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val)
    (inv := fun x => P1.WritesIn st s0 x.1 Wf)
  · rintro ⟨s', i⟩ hW'
    unfold msg.copy_mrs_loop1.body
    simp only at hW' ⊢
    by_cases hc1 : i < n
    · have hlt : i.val < n.val := (P1.gt_iff_val).1 hc1
      have hmax : msg.MSG_MAX_LENGTH.val = 120 := by unfold msg.MSG_MAX_LENGTH; rfl
      by_cases hc2 : i < msg.MSG_MAX_LENGTH
      · have hi120 : i.val < 120 := by rw [← hmax]; exact (P1.gt_iff_val).1 hc2
        simp only [hc1, hc2, ↓reduceIte]
        obtain ⟨i1, h1e, h1v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        rw [h1e, bind_ok]
        have hi1v : i1.val = i.val + 1 := by simpa using h1v
        refine WP.spec_bind (Endp.msg.buf_get.spec s' sw i1) ?_
        rintro v rfl
        refine WP.spec_bind (Endp.msg.buf_set.spec s' rw i1 _) ?_
        rintro s1 rfl
        rw [WP.spec_ok]
        have hW1 : P1.WritesIn st s' (L.wr s' (Endp.fl4BufA rw i1) (L.mem s' (Endp.fl4BufA sw i1))) Wf :=
          (P1.writesIn_wr (hal i1 (by omega))).mono fun b hb => hW b ⟨i1, by omega, hb⟩
        exact ⟨(hW'.trans hW1).mono fun b h => h.elim id id, by show n.val - i1.val < n.val - i.val; omega⟩
      · simp only [hc1, hc2, ↓reduceIte, WP.spec_ok]
        exact hW'
    · simp only [hc1, ↓reduceIte, WP.spec_ok]
      exact hW'
  · exact h

set_option maxHeartbeats 4000000 in
/-- **`do_ipc_transfer`'s footprint, a receiver with a buffer at `rw`, a
sender without a fault and no cap transferred** (`hcx`: with the grant, the
sender has no buffer or no extra caps): the receiver's registers and its
buffer words. -/
theorem do_ipc_transfer_rgB {T : Set U64} (hT : P1.TcbPlaced T) {snd rcv : U64} (hr : rcv ∈ T) (s : S) (a : A)
    (ep badge : U64) (grant : Bool) {rw : U64} (hrw0 : rw ≠ 0#u64)
    (hal : ∀ i : U64, i.val < 128 → P1.Aligned (Endp.fl4BufA rw i))
    (hb : msg.lookup_ipc_buffer st s true rcv ⦃ w => w = rw ⦄) (hf : L.mem s (tFaultA snd) = 0#u64)
    (hcx : grant = true → msg.lookup_ipc_buffer st s false snd ⦃ sw => sw = 0#u64 ∨
      (Fl4Spec.dataToMessageInfo (L.mem s (regA snd layout.reg.MSG_INFO)).bv).miExtraCaps = 0 ⦄) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => P1.WritesIn st s s' (XferBW T rw) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind hb ?_
  rintro rb hrb
  subst rb
  refine WP.spec_bind (obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  rw [hf, if_pos (by unfold fl4_abi.consts.fault.NullFault; rfl)]
  refine WP.spec_bind (Pₘ := fun sw => grant = true → sw = 0#u64 ∨
      (Fl4Spec.dataToMessageInfo (L.mem s (regA snd layout.reg.MSG_INFO)).bv).miExtraCaps = 0) ?_ ?_
  · cases grant with
    | false => exact WP.spec_mono (P0.msg.lookup_ipc_buffer.p0 st s false snd hS) fun _ _ h => absurd h (by simp)
    | true => exact WP.spec_mono (hcx rfl) fun _ h _ => h
  intro sw hsw
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨-, -, hext, hle⟩
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sw tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ e => e = ipc.NO_EXTRA_CAPS ⦄ := by
    cases grant with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have hc : sw = 0#u64 ∨ tag.extra_caps = 0#u64 := by
        rcases hsw rfl with h | h
        · exact Or.inl h
        · right; apply eq_of_bv; rw [hext, h]; rfl
      refine WP.spec_bind (lookup_extra_caps_none s snd sw tag hc) ?_
      rintro r rfl
      simp
  refine WP.spec_bind hex ?_
  rintro extra rfl
  refine WP.spec_bind (Pₘ := fun r : U64 × S => P1.WritesIn st s r.2 (XferBW T rw)) ?_ ?_
  · unfold msg.copy_mrs
    refine WP.spec_bind (copy_mrs_loop0_rg hT hr (P1.WritesIn.refl s _)) ?_
    rintro ⟨s1, i⟩ h1
    have h1' : P1.WritesIn st s s1 (XferBW T rw) := h1.mono fun b hb => Or.inl hb
    simp only [hrw0, ↓reduceIte]
    by_cases hsw0 : sw = 0#u64
    · simp only [hsw0, ↓reduceIte]
      first | exact (WP.spec_ok _).2 h1' | (simp only [WP.spec_ok]; exact h1')
    · simp only [hsw0, ↓reduceIte]
      exact copy_mrs_loop1_rb hal (fun b hb => Or.inr hb) s1 h1' sw _ i
  rintro ⟨n, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (transfer_caps_noextra (L := L) s1 tag ep rcv rw) ?_
  rintro ⟨out, s2⟩ hout
  simp only [Prod.mk.injEq] at hout
  obtain ⟨rfl, h2⟩ := hout
  subst s2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st s s3 (XferBW T rw)) ?_
    fun s3 h3 => WP.spec_mono (obj.Tcb.set_reg.rg (s := s3) (v := badge) hT hr
      (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s4 w4 => (h3.trans w4).mono fun b hb => hb.elim id Or.inl
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    WP.spec_mono (obj.Tcb.set_reg.rg (v := w) (s := s1) hT hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => (h1.trans w4).mono fun b hb => hb.elim id Or.inl

/-! ## A state with some words of another -/

/-- `s` with the words of `l` as in `t` (a fold of `L.wr`). -/
def mixS (s t : S) (l : List U64) : S := l.foldl (fun x b => L.wr x b (L.mem t b)) s

theorem mixS_cons (s t : S) (b : U64) (l : List U64) :
    mixS (L := L) s t (b :: l) = mixS (L := L) (L.wr s b (L.mem t b)) t l := rfl

theorem mixS_ksb (s t : S) (l : List U64) : L.ksb (mixS (L := L) s t l) = L.ksb s := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => rw [mixS_cons, ih]; simp

theorem mixS_cpu (s t : S) (l : List U64) : L.cpu (mixS (L := L) s t l) = L.cpu s := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => rw [mixS_cons, ih]; simp

theorem mixS_mem (s t : S) (l : List U64) (hl : ∀ b ∈ l, P1.Aligned b) {c : U64} (hc : P1.Aligned c) :
    L.mem (mixS (L := L) s t l) c = if c ∈ l then L.mem t c else L.mem s c := by
  induction l generalizing s with
  | nil => simp [mixS]
  | cons b l ih =>
    rw [mixS_cons, ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)), L.mem_wr _ _ _ _ (hl b (by simp)) hc]
    by_cases h1 : c ∈ l
    · simp [h1]
    · by_cases h2 : b = c
      · subst h2; simp
      · have h3 : c ≠ b := fun e => h2 e.symm
        simp [h1, h2, h3]

/-- The writes from `s` to `t` in `F` and `l`'s words, seen from `mixS s t l`: only `F`. -/
theorem mixS_writes {s t : S} {l : List U64} (hl : ∀ b ∈ l, P1.Aligned b) {F : U64 → Prop}
    (hw : P1.WritesIn st s t (fun b => F b ∨ b ∈ l)) : P1.WritesIn st (mixS (L := L) s t l) t F := by
  refine ⟨by rw [mixS_ksb]; exact hw.1, by rw [mixS_cpu]; exact hw.2.1, fun b hb hn => ?_⟩
  rw [mixS_mem s t l hl hb]
  split
  · rfl
  · rename_i h; exact hw.2.2 b hb (fun h' => h'.elim hn h)

/-- `s` to `mixS s t l`: only `l`'s words. -/
theorem mixS_from {s t : S} {l : List U64} (hl : ∀ b ∈ l, P1.Aligned b) :
    P1.WritesIn st s (mixS (L := L) s t l) (· ∈ l) := by
  refine ⟨mixS_ksb s t l, mixS_cpu s t l, fun b hb hn => ?_⟩
  rw [mixS_mem s t l hl hb, if_neg hn]

/-! ## P1 across the buffer words -/

/-- **The receiver's hole kept by the transfer with a receive buffer**: its
register writes (`xfer_all`) and buffer words lying outside the TCBs and
nodes, off the endpoints and notifications and the frame words (`capw_bx` for
the words of `Ω`, `xfer_all`'s `UserOK` for the others; the two write sets
split by `mixS`). -/
theorem blkX_bufw {T Cs Ω Sg Rp Scs Nt Ac X : Set U64} {H : P1.Heap} {Zb : U64 → Nat}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} {s1 s2 : S} {l : List U64}
    (h : P1.SchedQueuesInvX st T Cs Ω H X s1 Q R) (hB : P1.BoundInv st T Ac s1)
    (hX : P1.XInv st T Cs Ω Sg Rp Scs Nt Zb s1) (hS : P1.SCsOK st T Ω Sg Scs Zb Ac s1) (hSg : P1.SgOK st Ω Sg s1)
    (hl : ∀ b ∈ l, P1.OutsideObjs st T Cs s1 b ∧
      (∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧ b ∉ Sg)
    (hw : P1.WritesIn st s1 s2 (fun b => XferRegW T ∅ b ∨ b ∈ l)) :
    P1.SchedQueuesInvX st T Cs Ω H X s2 Q R ∧ P1.BoundInv st T Ac s2 ∧ P1.XInv st T Cs Ω Sg Rp Scs Nt Zb s2 ∧
      P1.SCsOK st T Ω Sg Scs Zb Ac s2 ∧ P1.SgOK st Ω Sg s2 ∧ L.actionW s2 = L.actionW s1 ∧
      L.curW s2 = L.curW s1 ∧ L.idleW s2 = L.idleW s1 ∧ L.cscW s2 = L.cscW s1 ∧
      (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K)) := by
  set lΩ := l.filter (fun b => decide (b ∈ Ω)) with hlΩ
  have halΩ : ∀ b ∈ lΩ, P1.Aligned b := fun b hb => (hl b (List.mem_of_mem_filter hb)).1.1
  set s1a := mixS (L := L) s1 s2 lΩ
  have w1 : P1.WritesIn st s1 s1a (· ∈ lΩ) := mixS_from halΩ
  obtain ⟨h1, hB1, hX1, hS1, hSg1, ec1, ecs1, ea1, ei1, f1, -⟩ := P1.capw_bx h hB hX hS hSg w1 fun b hb => by
    have hm := List.mem_filter.1 hb
    exact Or.inr ⟨by simpa using hm.2, (hl b hm.1).2.2⟩
  set U : Set U64 := {b | b ∈ l ∧ b ∉ Ω}
  have hU : P1.UserOK st T Cs Ω H U s1a := fun b hb =>
    ⟨(hl b hb.1).1.ksb (mixS_ksb s1 s2 lΩ), hb.2, (hl b hb.1).2.1⟩
  have w2 : P1.WritesIn st s1a s2 (P1.XferFoot T U) := by
    refine ⟨by rw [mixS_ksb]; exact hw.1, by rw [mixS_cpu]; exact hw.2.1, fun b hb hn => ?_⟩
    rw [mixS_mem s1 s2 lΩ halΩ hb]
    split
    · rfl
    · rename_i hnl
      refine hw.2.2 b hb fun h' => ?_
      rcases h' with h' | h'
      · rcases h' with ⟨y, hy, K, -, k2, k3, e⟩ | h''
        · exact hn (Or.inl ⟨y, hy, K, k2, k3, e⟩)
        · exact absurd h'' (Set.notMem_empty _)
      · by_cases hΩ : b ∈ Ω
        · exact hnl (List.mem_filter.2 ⟨h', by simpa using hΩ⟩)
        · exact hn (Or.inr ⟨h', hΩ⟩)
  obtain ⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, ecs2, f2, -⟩ := P1.xfer_all h1 hB1 hX1 hS1 hSg1 hU w2
  exact ⟨h2, hB2, hX2, hS2, hSg2, ea2.trans ea1, ec2.trans ec1, ei2.trans ei1, ecs2.trans ecs1,
    fun y hy K k1 k2 k3 => (f2 y hy K k1 k2 k3).trans (f1 y hy K (by omega) k2 k3)⟩


/-! ## The transfer into a receive buffer with its outcome as a state -/

/-- An `EpStep` changing the kheap at one object: the state is `σ` with user
memory and that object changed. -/
theorem epStep_form {σ σ' : Fl4Spec.State Unit} (h : EpStep σ σ') {p : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}
    (hk : σ'.kheap = Function.update σ.kheap p (some o)) :
    σ' = updK (Endp.setUm σ σ'.machineState.underlyingMemory) p o := by
  obtain ⟨h1, h2, -⟩ := h
  rcases σ' with ⟨a', e'⟩
  dsimp only at h1 h2 hk ⊢
  subst h1
  rw [hk] at h2
  rw [h2]
  rfl

theorem setReg2_eqA (x : Fl4Spec.Tcb) (v : Fl4Spec.Register → Fl4Spec.Word) (rs : List Fl4Spec.Register)
    (r1 : Fl4Spec.Register) (v1 : Fl4Spec.Word) (r2 : Fl4Spec.Register) (v2 : Fl4Spec.Word) :
    setReg (setReg (copyRegsTcb x v rs) r1 v1) r2 v2 =
      { x with tcbArch := (setReg (setReg (copyRegsTcb x v rs) r1 v1) r2 v2).tcbArch } := by
  rw [copyRegsTcb_other]; rfl

set_option maxHeartbeats 8000000 in
/-- **EpXferBuf2's `do_ipc_transfer_buf` with the spec's outcome as a state**:
`σ` with user memory changed and the receiver's TCB changed in its user
context only (`copy_mrs_rel`'s `EpStep`, `epStep_form`). -/
theorem do_ipc_transfer_bufE {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {SR : S → Fl4Spec.State Unit → Prop} (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (epo : Option Fl4Spec.ObjRef := some ep.bv) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ (x' : Fl4Spec.Tcb) (um : Fl4Spec.Word → Fl4Spec.Word8),
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ =
        ({((), updK (Endp.setUm σ um) rcv.bv (.tcb x'))}, False) ∧
      EpStateRel T E R B (L.mem s') (updK (Endp.setUm σ um) rcv.bv (.tcb x')) ∧
      SR s' (updK (Endp.setUm σ um) rcv.bv (.tcb x')) ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      x' = { xr with tcbArch := x'.tcbArch } ⦄ := by
  have hra := hP.tcb rcv hr
  have hxs := hR.at_tcb hs hks
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  have hu := hBm.frame s σ rcv xr rp hR hSR hr hkr hrb
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (hBm.lookupMap s σ rcv xr true rp hR hSR hr hkr hrb) ?_
  rintro rw ⟨hrw0, hmr⟩
  refine WP.spec_bind (obj.Tcb.fault_type.spec (L := L) s snd) ?_
  intro ft hft
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_send_buf hBf hBm s σ hR hSR hs hks) ?_
  rintro sw hsw
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sw tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ e => e = ipc.NO_EXTRA_CAPS ⦄ := by
    cases grant with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have hc : sw = 0#u64 ∨ tag.extra_caps = 0#u64 := by
        rcases hcaps with h | h | h
        · cases h
        · rcases hsw with ⟨-, h'⟩ | ⟨sp, h', -⟩
          · exact Or.inl h'
          · rw [h] at h'; cases h'
        · right; apply eq_of_bv; rw [hext, hwmi]; apply BitVec.eq_of_toNat_eq; exact h
      refine WP.spec_bind (lookup_extra_caps_none s snd sw tag hc) ?_
      rintro r rfl
      simp
  refine WP.spec_bind hex ?_
  rintro extra rfl
  refine WP.spec_bind (copy_mrs_rel hH hP s σ hR hSR hs hr hne hks hkr hmr hrw0 hu hsw tag.length hle) ?_
  rintro ⟨n, s1⟩ ⟨σc, hcopy, hkcf, hRc, hSc, hAc, hn, -, hE⟩
  simp only at hcopy hkcf hRc hSc hAc hn
  have hkc : σc.kheap rcv.bv = some (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
      (Fl4Spec.msg_registers.take tag.length.val))) := by rw [hkcf]; simp
  refine WP.spec_bind (transfer_caps_noextra (L := L) s1 tag ep rcv rw) ?_
  rintro ⟨out, s2⟩ hout
  simp only [Prod.mk.injEq] at hout
  obtain ⟨rfl, h2⟩ := hout
  subst s2
  show (do
    let s3 ← msg.set_msg_info st s1 rcv
      { label := tag.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := n }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  refine WP.spec_bind (set_msg_info_spec (L := L) s1 rcv tag.label n (by omega)) ?_
  rintro s3 ⟨v, hs3, hv⟩
  refine WP.spec_mono (obj.Tcb.set_reg.spec (L := L) s3 rcv layout.reg.BADGE badge) ?_
  intro s4 hs4
  subst hs3 hs4
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  set x1 := copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take tag.length.val)
  have hlenw : tag.length.bv = (Fl4Spec.dataToMessageInfo w).miLength := by rw [hlen, hwmi]
  -- the receive slots
  obtain ⟨sl, hsl⟩ := hBm.recvSlots s1 σc rcv x1 rp hRc hSc hr hkc (by rw [ipcBufOf_copyRegs]; exact hrb)
  have hcopy' := hcopy
  rw [hlenw] at hcopy'
  have hspec := doIpcTransfer_recvBuf hks hkr hf hrb epo badge.bv grant hcaps hcopy' hkc hsl
  -- the two register writes
  obtain ⟨hR2, hW2, hS2⟩ := write_reg_rel hP s1 _ hRc hr hkc Fl4Spec.msg_info_register v
  rw [regIdx_msgInfo] at hR2 hW2
  have hkc2 : (updK σc rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp
  obtain ⟨hR3, hW3, hS3⟩ := write_reg_rel hP _ _ hR2 hr hkc2 Fl4Spec.badge_register badge
  rw [regIdx_badge] at hR3 hW3
  have hvx : v.bv = Fl4Spec.messageInfoToData ⟨n.bv, 0, 0, (Fl4Spec.dataToMessageInfo w).miLabel⟩ := by
    rw [hv]; congr 2; rw [hlab, hwmi]; rfl
  have hfin : updK (updK σc rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      updK σc rcv.bv (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register (Fl4Spec.messageInfoToData
        ⟨n.bv, 0, 0, (Fl4Spec.dataToMessageInfo w).miLabel⟩)) Fl4Spec.badge_register badge.bv)) := by
    simp only [updK, Function.update_idem]; rw [hvx]
  rw [hfin] at hR3
  have hS := hH.stable _ _ _ _ (hH.stable _ _ _ _ hSc hW2 hS2) hW3 hS3
  rw [hfin] at hS
  obtain ⟨um, hσc⟩ : ∃ um, σc = updK (Endp.setUm σ um) rcv.bv (.tcb x1) := ⟨_, epStep_form hE hkcf⟩
  have hfe : ∀ o, updK σc rcv.bv o = updK (Endp.setUm σ um) rcv.bv o := fun o => by
    rw [hσc]; simp only [updK, Function.update_idem]
  rw [hfe] at hspec hR3 hS
  refine ⟨_, um, hspec, hR3, hS, ?_, ?_⟩
  · intro b hb hn'
    have hn1 : ¬ RcvMR rcv b := fun ⟨r, _, h⟩ => hn'.1 ⟨r, h⟩
    rw [← regIdx_badge, ← regIdx_msgInfo,
      rd_wr_ne (a_reg hra Fl4Spec.badge_register).1 hb (fun h => hn'.1 ⟨Fl4Spec.badge_register, by rw [← h]⟩),
      rd_wr_ne (a_reg hra Fl4Spec.msg_info_register).1 hb (fun h => hn'.1 ⟨Fl4Spec.msg_info_register, by rw [← h]⟩)]
    exact hAc b hb ⟨hn1, hn'.2⟩
  · exact setReg2_eqA xr _ _ _ _ _ _


/-! ## Back to `JAtZ`: the buffer words written first -/

set_option maxHeartbeats 16000000 in
/-- The receiver's buffer words of a list written at `J` with the values of
`t`, each by `JAtZ.userWrJ` (the spec changing only user memory). -/
theorem JAtZ.bufWrites {d : U64} (hdT : d ∈ Z.T) (hdth : Z.th d = some .tcb)
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) {rp : Fl4Spec.ObjRef}
    (hrp : Endp.ipcBufOf true xd = some rp) (t : S) :
    ∀ (l : List U64), (∀ b ∈ l, RBufW ⟨rp⟩ b) → ∀ (s0 : S) (um : Fl4Spec.Word → Fl4Spec.Word8),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a (Endp.setUm σ um) →
      ∃ um', JAtZ (L := L) arI AR Z H Cs Ac Lst D (mixS (L := L) s0 t l) a (Endp.setUm σ um') := by
  intro l
  induction l with
  | nil => intro _ s0 um J0; exact ⟨um, J0⟩
  | cons b l ih =>
    intro hl s0 um J0
    obtain ⟨i, hi, rfl⟩ := hl _ (List.mem_cons_self ..)
    obtain ⟨hOK, hBC, hBP⟩ := J0.xferH
    have hkd' : (Endp.setUm σ um).kheap d.bv = some (.tcb xd) := hkd
    have hwB : (Endp.fl4BufA ⟨rp⟩ i, Endp.bufAddr rp i.val) ∈ Z.B := hBC d hdT xd true rp hkd' hrp ⟨rp⟩ rfl i hi
    obtain ⟨hAp, hObj⟩ := J0.bufWord hOK hdth hkd' hrp i.val hi (b := Endp.fl4BufA ⟨rp⟩ i) (by rw [fl4BufA_bv])
    have J1 := J0.userWrJ hBP hwB hAp hObj (L.mem t (Endp.fl4BufA ⟨rp⟩ i))
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ _ J1

set_option maxHeartbeats 16000000 in
/-- **Back to `JAtZ` across the receiver's buffer words** (module
docstring): from `J` at `s` and a state `s'` written from `s` in `CnW` (and
`KW`) and the buffer words, `JAtZ` at `mixS s s'` (the buffer words of `s'`
written at `J`, `JAtZ.bufWrites`) with the spec's user memory changed, from
which `s'` writes only in `CnW` and `KW`. -/
theorem JAtZ.bufRebase (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {d : U64}
    (hdT : d ∈ Z.T) (hdth : Z.th d = some .tcb) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd))
    {rp : Fl4Spec.ObjRef} (hrp : Endp.ipcBufOf true xd = some rp) {s' : S}
    (hw : P1.WritesIn st s s' (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RBufW ⟨rp⟩ b))
    (hfoot : P1.WritesIn st s s' (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s b ∨ RBufW ⟨rp⟩ b)) :
    ∃ (su : S) (um : Fl4Spec.Word → Fl4Spec.Word8), JAtZ (L := L) arI AR Z H Cs Ac Lst D su a (Endp.setUm σ um) ∧
      P1.WritesIn st su s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c su (Endp.setUm σ um)) ∧
      P1.WritesIn st su s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
        (P1.EH H) su) ∧
      L.ksb su = L.ksb s ∧ (∀ b, P1.Aligned b → ¬ RBufW ⟨rp⟩ b → L.mem su b = L.mem s b) := by
  obtain ⟨-, hBC, -⟩ := J.xferH
  have hal : ∀ b ∈ rbList ⟨rp⟩, P1.Aligned b := fun b hb => by
    obtain ⟨i, hi, rfl⟩ := mem_rbList.1 hb
    exact (J.xtop.fin.1.2.ep.balign _ (hBC d hdT xd true rp hkd hrp ⟨rp⟩ rfl i hi)).1
  obtain ⟨um, Ju⟩ := JAtZ.bufWrites hdT hdth hkd hrp s' (rbList ⟨rp⟩) (fun b hb => mem_rbList.1 hb) s
    σ.machineState.underlyingMemory J
  have hks : L.ksb (mixS (L := L) s s' (rbList ⟨rp⟩)) = L.ksb s := mixS_ksb _ _ _
  refine ⟨_, um, Ju, ?_, ?_, hks, fun b hb hn => ?_⟩
  · refine (mixS_writes hal (hw.mono fun b hb => hb.imp_right mem_rbList.2)).mono fun b hb => ?_
    exact cnW_back (s := mixS (L := L) s s' (rbList ⟨rp⟩)) (s' := s) (σ := Endp.setUm σ um) (σ' := σ) hks.symm
      (fun sc _ x n hk => ⟨x, hk⟩) hb
  · refine (mixS_writes hal (hfoot.mono fun b hb => hb.imp_right mem_rbList.2)).mono fun b hb => ?_
    have e : ∀ c o, L.nodeAt (mixS (L := L) s s' (rbList ⟨rp⟩)) c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
    unfold P1.KW at hb ⊢
    simp only [e]; exact hb
  · rw [mixS_mem s s' _ hal hb, if_neg (fun h => hn (mem_rbList.1 h))]


/-! ## The uniform transfer step -/

/-- The receiver's buffer words (none without a receive buffer). -/
def RcvBufW (xd : Fl4Spec.Tcb) (b : U64) : Prop := ∃ rp, Endp.ipcBufOf true xd = some rp ∧ RBufW ⟨rp⟩ b

/-- **No cap transferred**: no grant, no sender buffer, no extra caps, or
no receive buffer. -/
def XferNoCap (g : Bool) (xs xd : Fl4Spec.Tcb) : Prop :=
  g = false ∨ Endp.ipcBufOf false xs = none ∨
    Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0 ∨
    Endp.ipcBufOf true xd = none

theorem setUm_self (σ0 : Fl4Spec.State Unit) : Endp.setUm σ0 σ0.machineState.underlyingMemory = σ0 := rfl

set_option maxHeartbeats 8000000 in
/-- The receiver's buffer words at `J` are untracked for P1 (`JAtZ.bufWord`,
`JAtZ`'s `nodeB`). -/
theorem JAtZ.rbufU (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {d : U64}
    (hdT : d ∈ Z.T) (hdth : Z.th d = some .tcb) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) :
    ∀ b, RcvBufW xd b → P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b ∧
      (∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧ b ∉ P1.Heap.frame H := by
  rintro b ⟨rp, hrp, i, hi, rfl⟩
  obtain ⟨hOK, hBC, -⟩ := J.xferH
  have hwB := hBC d hdT xd true rp hkd hrp ⟨rp⟩ rfl i hi
  have hal := (J.xtop.fin.1.2.ep.balign _ hwB).1
  obtain ⟨hAp, -⟩ := J.bufWord hOK hdth hkd hrp i.val hi (b := Endp.fl4BufA ⟨rp⟩ i) (by rw [fl4BufA_bv])
  refine ⟨⟨hal, fun t ht => ?_, fun c hc => ?_⟩, fun e he => ?_, fun hf => ?_⟩
  · rcases hAp t .tcb ht (fun _ e => by cases e) with e | e
    · left; omega
    · right; simpa [P1.HKind.bits] using e
  · have e := J.nodeB _ hwB c (J.kern.csLt c hc)
    dsimp only at e
    rcases e with e | e <;> omega
  · rcases he with he | he
    · rcases hAp e _ he (fun _ e => by cases e) with e | e
      · left; omega
      · right; simp only [P1.HKind.bits] at e; omega
    · rcases hAp e _ he (fun _ e => by cases e) with e | e
      · left; omega
      · right; simp only [P1.HKind.bits] at e; omega
  · obtain ⟨-, p, k, hp, hk, hin⟩ := hf
    have hko : ∀ z, k ≠ .other z := by
      rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
    obtain ⟨g1, g2⟩ := hin
    rcases hAp p k hp hko with e | e <;> omega

set_option maxHeartbeats 8000000 in
/-- `JAtZ.bufRebase` for the receiver's buffer words, none or some. -/
theorem JAtZ.bufRebaseX (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {d : U64}
    (hdT : d ∈ Z.T) (hdth : Z.th d = some .tcb) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) {s' : S}
    (hw : P1.WritesIn st s s' (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b))
    (hfoot : P1.WritesIn st s s' (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s b ∨ RcvBufW xd b)) :
    ∃ (su : S) (um : Fl4Spec.Word → Fl4Spec.Word8), JAtZ (L := L) arI AR Z H Cs Ac Lst D su a (Endp.setUm σ um) ∧
      P1.WritesIn st su s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c su (Endp.setUm σ um)) ∧
      P1.WritesIn st su s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
        (P1.EH H) su) ∧ L.ksb su = L.ksb s ∧ (∀ b, P1.Aligned b → ¬ RcvBufW xd b → L.mem su b = L.mem s b) := by
  cases hrp : Endp.ipcBufOf true xd with
  | none =>
    have hn : ∀ b, ¬ RcvBufW xd b := fun b ⟨rp, h, _⟩ => by rw [hrp] at h; cases h
    exact ⟨s, σ.machineState.underlyingMemory, J, hw.mono fun b hb => hb.resolve_right (hn b),
      hfoot.mono fun b hb => hb.resolve_right (hn b), rfl, fun _ _ _ => rfl⟩
  | some rp =>
    have hc : ∀ b, RcvBufW xd b → RBufW ⟨rp⟩ b := fun b ⟨rp', h, hb⟩ => by rw [hrp] at h; cases h; exact hb
    obtain ⟨su, um, Ju, h1, h2, h3, h4⟩ := J.bufRebase hdT hdth hkd hrp
      (hw.mono fun b hb => hb.imp_right (hc b)) (hfoot.mono fun b hb => hb.imp_right (hc b))
    exact ⟨su, um, Ju, h1, h2, h3, fun b hb hn => h4 b hb fun h => hn ⟨rp, hrp, h⟩⟩

set_option maxHeartbeats 16000000 in
/-- **The transfer step of `send_ipc` to a waiting receiver, with or without
a receive buffer, no cap transferred** (module docstring): on `IRel` by
`do_ipc_transfer_regsJ` (no buffer) or `do_ipc_transfer_bufE` (a buffer),
the footprint `XferRegW ∪ RcvBufW` (`do_ipc_transfer_rg`,
`do_ipc_transfer_rgB`), P1's hole by `xfer_all` or `blkX_bufw`. -/
theorem xferStepJ {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} {c : U64} (hP0 : Ipc.IPlaced N T E R B) (hP : EPlaced T E R B)
    (hHE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover T B σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (ep badge : U64) (grant : Bool) (hnc : XferNoCap grant xs xr)
    {T1 Cs1 Ω Sg Rp Scs Nt Ac1 X : Set U64} {H1 : P1.Heap} {Zb : U64 → Nat} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} (hT1 : P1.TcbPlaced T1) (hr1 : rcv ∈ T1)
    (h : P1.SchedQueuesInvX st T1 Cs1 Ω H1 X s Q Rq) (hB : P1.BoundInv st T1 Ac1 s)
    (hX : P1.XInv st T1 Cs1 Ω Sg Rp Scs Nt Zb s) (hS : P1.SCsOK st T1 Ω Sg Scs Zb Ac1 s) (hSg : P1.SgOK st Ω Sg s)
    (hU : ∀ b, RcvBufW xr b → P1.OutsideObjs st T1 Cs1 s b ∧
      (∀ e, (H1 e = some .ep ∨ H1 e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧ b ∉ Sg) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ (x' : Fl4Spec.Tcb)
      (um : Fl4Spec.Word → Fl4Spec.Word8),
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), updK (Endp.setUm σ um) rcv.bv (.tcb x'))}, False) ∧ x' = { xr with tcbArch := x'.tcbArch } ∧
      EpStateRel T E R B (L.mem s') (updK (Endp.setUm σ um) rcv.bv (.tcb x')) ∧
      (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s' (updK (Endp.setUm σ um) rcv.bv (.tcb x')) ∧
        Endp.IpcBufCapOK (updK (Endp.setUm σ um) rcv.bv (.tcb x'))) ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      P1.WritesIn st s s' (fun b => XferRegW T1 ∅ b ∨ RcvBufW xr b) ∧
      P1.SchedQueuesInvX st T1 Cs1 Ω H1 X s' Q Rq ∧ P1.BoundInv st T1 Ac1 s' ∧ P1.XInv st T1 Cs1 Ω Sg Rp Scs Nt Zb s' ∧
      P1.SCsOK st T1 Ω Sg Scs Zb Ac1 s' ∧ P1.SgOK st Ω Sg s' ∧
      (∀ y ∈ T1, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ⦄ := by
  have hf1 : L.mem s (tFaultA snd) = 0#u64 := (hR.at_tcb hs hks).fault0.2 hf
  obtain ⟨⟨⟨G, hBt⟩, hBw⟩, -⟩ := hSR.1.1
  cases hrb : Endp.ipcBufOf true xr with
  | none =>
    have hlk : msg.lookup_ipc_buffer st s true rcv ⦃ w => w = 0#u64 ⦄ :=
      WP.spec_mono (lookup_buf_full s σ hBt.2.1.1 hBt.2.1.2.1 (Ipc.RelTopB.tcbT hBt hkr) hkr hOK true)
        fun w hw => hw.1.2 hrb
    refine WP.spec_mono (WP.spec_and (do_ipc_transfer_regsJ hP0 hP hHE s a σ hR hSR hOK hBC hs hr hne hks hkr hf hrb
      ep badge grant) (do_ipc_transfer_rg (arI := arI) hT1 hr1 s a ep badge grant hlk hf1)) ?_
    rintro s2 ⟨⟨e2, hR2, hS2, hA2⟩, w2⟩
    obtain ⟨h2, hB2, hX2, hS2', hSg2, -, -, -, -, f2, -⟩ :=
      P1.xfer_all h hB hX hS hSg (U := ∅) (fun b hb => absurd hb (Set.notMem_empty _))
        (w2.mono fun b hb => P1.XferRegW.foot hb)
    refine ⟨xferTcb xr xs badge.bv, σ.machineState.underlyingMemory, e2, xferTcb_eqA _ _ _, hR2, hS2,
      fun b hb hn => hA2 b hb hn.1, w2.mono fun b hb => Or.inl hb, h2, hB2, hX2, hS2', hSg2, f2⟩
  | some rp =>
    have hcaps : grant = false ∨ Endp.ipcBufOf false xs = none ∨
        Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0 := by
      rcases hnc with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
      · rw [hrb] at h'; cases h'
    have hlb := lookup_buf_full s σ hBt.2.1.1 hBt.2.1.2.1 (Ipc.RelTopB.tcbT hBt hkr) hkr hOK true
    obtain ⟨x0, hk0, hbw⟩ := hBw.bw rcv hr
    rw [hkr] at hk0; cases hk0
    have hlk : msg.lookup_ipc_buffer st s true rcv ⦃ w => w = ⟨rp⟩ ⦄ := WP.spec_mono hlb fun w hw => by
      have hwb : w.bv = rp := hw.2 hbw rp hrb
      rw [← hwb]
    have hrw0 : (⟨rp⟩ : U64) ≠ 0#u64 := by
      obtain ⟨w0, -, hw0⟩ := spec_exists hlb
      have hwb : w0.bv = rp := hw0.2 hbw rp hrb
      intro e
      have : w0 = 0#u64 := by rw [← e, ← hwb]
      rw [hw0.1.1 this] at hrb; cases hrb
    have hal : ∀ i : U64, i.val < 128 → P1.Aligned (Endp.fl4BufA ⟨rp⟩ i) := fun i hi =>
      (hP.balign _ (hBC rcv hr xr true rp hkr hrb ⟨rp⟩ rfl i hi)).1
    have hxs := hR.at_tcb hs hks
    have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
      rw [← regIdx_msgInfo]; exact hxs.regs _
    have hcx : grant = true → msg.lookup_ipc_buffer st s false snd ⦃ sw => sw = 0#u64 ∨
        (Fl4Spec.dataToMessageInfo (L.mem s (regA snd layout.reg.MSG_INFO)).bv).miExtraCaps = 0 ⦄ := by
      intro hg
      rcases hcaps with h' | h' | h'
      · rw [hg] at h'; cases h'
      · have hlf := lookup_buf_full s σ hBt.2.1.1 hBt.2.1.2.1 (Ipc.RelTopB.tcbT hBt hks) hks hOK false
        exact WP.spec_mono hlf fun w hw => Or.inl (hw.1.2 h')
      · have hlf := lookup_buf_full s σ hBt.2.1.1 hBt.2.1.2.1 (Ipc.RelTopB.tcbT hBt hks) hks hOK false
        refine WP.spec_mono hlf fun w _ => Or.inr ?_
        rw [hwmi]; apply BitVec.eq_of_toNat_eq; exact h'
    refine WP.spec_mono (WP.spec_and (do_ipc_transfer_bufE (arI := arI) (epHyps_bufC hHE T) (epBufHyps_bufC T)
      (epBufMapHyps_bufC hP0) hP s a σ hR ⟨⟨hSR.1, hOK⟩, hBC⟩ hs hr hne hks hkr hf hrb ep badge grant hcaps)
      (do_ipc_transfer_rgB (arI := arI) hT1 hr1 s a ep badge grant hrw0 hal hlk hf1 hcx)) ?_
    rintro s2 ⟨⟨x', um, e2, hR2, hS2, hA2, hx'⟩, w2⟩
    have hW : P1.WritesIn st s s2 (fun b => XferRegW T1 ∅ b ∨ RcvBufW xr b) :=
      w2.mono fun b hb => hb.imp_right fun h' => ⟨rp, hrb, h'⟩
    obtain ⟨h2, hB2, hX2, hS2', hSg2, -, -, -, -, f2⟩ := blkX_bufw (l := rbList ⟨rp⟩) h hB hX hS hSg
      (fun b hb => hU b ⟨rp, hrb, mem_rbList.1 hb⟩) (w2.mono fun b hb => hb.imp_right mem_rbList.2)
    exact ⟨x', um, e2, hx', hR2, hS2.1, hA2, hW, h2, hB2, hX2, hS2', hSg2, f2⟩


/-! ## Helpers for the callers -/

@[simp] theorem setUm_kheap' (σ0 : Fl4Spec.State Unit) (um : Fl4Spec.Word → Fl4Spec.Word8) :
    (Endp.setUm σ0 um).kheap = σ0.kheap := rfl

/-- A `DWFr` frame from a state with other user memory. -/
theorem DWFr.ofUm {r t : Fl4Spec.ObjRef} {σ0 σ' : Fl4Spec.State Unit} (F : DWFr r t σ0 σ')
    (um : Fl4Spec.Word → Fl4Spec.Word8) : DWFr r t (Endp.setUm σ0 um) σ' :=
  ⟨⟨F.sk.ct, F.sk.idle, F.sk.cons, F.sk.tm, F.sk.csc, F.sk.cdt, F.sk.orig, F.sk.arch, F.sk.dt, F.sk.isc⟩,
    F.rel, F.kh, F.tsc, F.scb⟩

/-- `Foot.trans` with extra words `W` on both sides. -/
theorem footW_trans {T1 Cs1 Sg Scs Es : Set U64} {Zb : U64 → Nat} {W : U64 → Prop} {s1 s2 s3 : S}
    (h1 : P1.WritesIn st s1 s2 (fun b => P1.KW st T1 Cs1 Sg Scs Zb Es s1 b ∨ W b))
    (h2 : P1.WritesIn st s2 s3 (fun b => P1.KW st T1 Cs1 Sg Scs Zb Es s2 b ∨ W b)) :
    P1.WritesIn st s1 s3 (fun b => P1.KW st T1 Cs1 Sg Scs Zb Es s1 b ∨ W b) :=
  (h1.trans h2).mono fun b hb => hb.elim id fun hb => hb.imp_left (P1.KW.ksb h1.1)


theorem CFr.um (r t : Fl4Spec.ObjRef) (σ0 : Fl4Spec.State Unit) (um : Fl4Spec.Word → Fl4Spec.Word8) :
    CFr r t σ0 (Endp.setUm σ0 um) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => Or.inl rfl⟩

theorem IK.um (t : Fl4Spec.ObjRef) (σ0 : Fl4Spec.State Unit) (um : Fl4Spec.Word → Fl4Spec.Word8) :
    IK t σ0 (Endp.setUm σ0 um) := IK.of_eq rfl rfl rfl rfl

theorem SKeep.um (σ0 : Fl4Spec.State Unit) (um : Fl4Spec.Word → Fl4Spec.Word8) : SKeep σ0 (Endp.setUm σ0 um) :=
  ⟨rfl, rfl, fun _ y h => ⟨y, h, rfl⟩, fun _ _ _ h => h⟩


/-- A `Foot` as a footprint with extra words. -/
theorem footW_of {T1 Cs1 Sg Scs Es : Set U64} {Zb : U64 → Nat} {W : U64 → Prop} {s1 s2 : S}
    (h : P1.Foot st T1 Cs1 Sg Scs Zb Es s1 s2) :
    P1.WritesIn st s1 s2 (fun b => P1.KW st T1 Cs1 Sg Scs Zb Es s1 b ∨ W b) :=
  P1.WritesIn.mono h fun _ hb => Or.inl hb

end

end

end Fl4Proofs.P3
