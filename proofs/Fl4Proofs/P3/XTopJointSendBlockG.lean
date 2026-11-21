/-
P3 (DESIGN.md §9), IPC: **the timeout handler's blocking send at `J`**
(`JAtZ.runTmoJ`; toward XTopJointIpcJ's `JReplyRestHyp`: the reply tail's
`handle_timeout` of the receiver, which is not the current thread, has just
been made `Running` or `Restart`, and whose SC is not released). The
variant of XTopJointSendBlock's `JAtZ.sendBlockJ` for a thread other than
the current one, fused with the `set_thread_state` before it and the
timeout fault's `set_fault`, as XTopJointRunPost's `JAtZ.runPostJ` fuses
`postpone` (the states between are no `J` states: the thread's SC is not
released, so `Inv.rd` fails there).

* `set_fault_timeout_eq`: FL4's `set_fault` of a timeout fault is the four
  fault-word writes.
* `BFrT t e`: the spec's frame of the whole step (`Sk`; `t`'s TCB to
  `blockedOnSend` with its fault changed, `e`'s endpoint), with what it
  keeps (as XTopJointSendBlock's `BFr`).
* `JAtZ.runTmoJ`: `set_thread_state` (P1's `BlkOK` step given, `hB`; the
  state after `XTopAt` and `IRel` for the tail's reads), then
  `handle_timeout`: the timeout-handler slot's cap (an endpoint cap,
  `hth`), `set_fault` (`set_fault_timeout_top`; P1 `faults.set_fault.blk`),
  `send_ipc` blocking on an idle or sending endpoint (`hcb`;
  XTopJointSendBlock's `send_ipc_blockF`, `sendIpcBlock_eq`; P1
  `endpoint.send_ipc.block` with `CanBlock` of the thread: not queued, not
  in the release queue, the action not it, not idle, its SC active), ending
  at `JAtZ` with the endpoint out of the dead set (covered by the handler
  cap, `JAtZ.cover_cap`). `Inv` by `InvBut.ik` (`IK` of the three spec
  steps) and the weakened `Inv.rd` (the thread is a sender with a timeout
  fault, `inClassR`, l4v `valid_sender_sc_tcb_at`); `BlockedScActive` from
  the thread's active SC.
-/
import Fl4Proofs.P3.XTopJointSendBlock
import Fl4Proofs.P3.XTopJointStsI
import Fl4Proofs.P3.IpcTimeout
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`set_fault` of a timeout fault** writes the four fault words. -/
theorem set_fault_timeout_eq (s : S) (t : U64) (b : U64) :
    faults.set_fault st s t (error.Fault.Timeout b) ⦃ s' => s' =
      L.wr (L.wr (L.wr (L.wr s (tFaultA t) fl4_abi.consts.fault.Timeout) (tFw0A t) b) (tFw1A t) 0#u64)
        (tFw2A t) 0#u64 ⦄ := by
  unfold faults.set_fault
  simp only [bind_ok]
  step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s1, hs1⟩
  step with set_fault_w0_spec as ⟨s2, hs2⟩
  step with set_fault_w1_spec as ⟨s3, hs3⟩
  refine WP.spec_mono (set_fault_w2_spec s3 t 0#u64) ?_
  rintro s4 rfl
  subst hs1 hs2 hs3
  rfl

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- **One object's change by the timeout handler's blocking send**: `t`'s
TCB to `blockedOnSend` with its fault changed, or `e`'s endpoint. -/
def BChgT (t e p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x ep d f, o = .tcb x ∧ o' = .tcb { x with tcbState := .blockedOnSend ep d, tcbFault := f } ∧ p = t) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ p = e)

/-- **The spec's frame of the timeout handler's blocking send** (module
docstring). -/
structure BFrT (t e : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ BChgT t e p o o'

theorem BChgT.objFrK {t e p : ObjRef} {o o' : KernelObject} (h : BChgT t e p o o') : IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, _, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩
  · exact IpcFrKeep.objFrK_tcb rfl rfl
  · exact IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrT.ipcFr {t e : ObjRef} {σ σ' : State Unit} (F : BFrT t e σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK

section
variable {t e : ObjRef} {σ σ' : State Unit}

theorem BFrT.tcbF (h : BFrT t e σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ (y = x ∨ (p = t ∧ ∃ ep d f, 
      y = { x with tcbState := .blockedOnSend ep d, tcbFault := f })) := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [h1, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', ep, d, f, e1, rfl, hp'⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨_, h2, Or.inr ⟨hp', ep, d, f, rfl⟩⟩

theorem BFrT.tcbB (h : BFrT t e σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ (y = x ∨ (p = t ∧ ∃ ep d f, 
      y = { x with tcbState := .blockedOnSend ep d, tcbFault := f })) := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← h1, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, ep, d, f, rfl, e2, hp'⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, h1, Or.inr ⟨hp', ep, d, f, rfl⟩⟩

/-- The other kinds kept. -/
theorem BFrT.othF (h : BFrT t e σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h4 : ∀ x, o ≠ .endpoint x) : σ'.kheap p = some o := by
  rcases h.kh p with e' | ⟨o0, o', k1, k2, hc⟩
  · rw [e', hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, _, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h4 _)

theorem BFrT.othB (h : BFrT t e σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h4 : ∀ x, o' ≠ .endpoint x) : σ.kheap p = some o' := by
  rcases h.kh p with e' | ⟨o, o'', k1, k2, hc⟩
  · rw [← e', hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h4 _)

theorem BFrT.scF (h : BFrT t e σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) : σ'.kheap p = some (.schedContext y n) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrT.scB (h : BFrT t e σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrT.replyF (h : BFrT t e σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    σ'.kheap p = some (.reply x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrT.replyB (h : BFrT t e σ σ') {p : ObjRef} {x : Reply} (hp : σ'.kheap p = some (.reply x)) :
    σ.kheap p = some (.reply x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrT.ntfnF (h : BFrT t e σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    σ'.kheap p = some (.notification x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrT.ntfnB (h : BFrT t e σ σ') {p : ObjRef} {x : Notification} (hp : σ'.kheap p = some (.notification x)) :
    σ.kheap p = some (.notification x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrT.epF (h : BFrT t e σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ p = e) := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [h1, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, e1, -⟩ | ⟨x', y, e1, rfl, hp'⟩ <;> cases e1
    exact ⟨y, h2, Or.inr hp'⟩

theorem BFrT.epB (h : BFrT t e σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ p = e) := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← h1, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hp'⟩ <;> cases e2
    exact ⟨x, h1, Or.inr hp'⟩

theorem BFrT.kind (h : BFrT t e σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e', ho], rfl⟩, fun o' ho => ⟨o', by rw [← e', ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, ep, d, f, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

theorem BFrT.szKeep (h : BFrT t e σ σ') : SzKeep σ σ' := fun _ y n hp => ⟨y, h.scB hp⟩

theorem BFrT.ykeep (h : BFrT t e σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ⟨y, h.scF hp, rfl⟩, fun p z n hp => ⟨z, h.scB hp, rfl⟩⟩
  obtain ⟨y, hp', hy⟩ := h.tcbF hp
  rcases hy with rfl | ⟨-, ep, d, f, rfl⟩
  · exact ⟨_, hp', rfl⟩
  · exact ⟨_, hp', rfl⟩

theorem BFrT.mcpKeep (h : BFrT t e σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨y, hp', hy⟩ := h.tcbF hp
  rcases hy with rfl | ⟨-, ep, d, f, rfl⟩
  · exact ⟨_, hp', rfl⟩
  · exact ⟨_, hp', rfl⟩

theorem BFrT.bufKeep (h : BFrT t e σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by
    obtain ⟨y, hp', hy⟩ := h.tcbF hp
    rcases hy with rfl | ⟨-, ep, d, f, rfl⟩
    · exact ⟨_, hp', rfl⟩
    · exact ⟨_, hp', rfl⟩

theorem BFrT.tcbSc (h : BFrT t e σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbPriority = x.tcbPriority := by
  obtain ⟨y, hp', hy⟩ := h.tcbF hp
  rcases hy with rfl | ⟨-, ep, d, f, rfl⟩
  · exact ⟨_, hp', rfl, rfl⟩
  · exact ⟨_, hp', rfl, rfl⟩

theorem BFrT.tcbScB (h : BFrT t e σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbPriority = x.tcbPriority := by
  obtain ⟨x, hp', hy⟩ := h.tcbB hp
  rcases hy with rfl | ⟨-, ep, d, f, rfl⟩
  · exact ⟨_, hp', rfl, rfl⟩
  · exact ⟨_, hp', rfl, rfl⟩

/-- A TCB other than `t`, kept. -/
theorem BFrT.tcbO (h : BFrT t e σ σ') {p : ObjRef} (hpt : p ≠ t) {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    σ'.kheap p = some (.tcb x) := by
  obtain ⟨y, hp', hy⟩ := h.tcbF hp
  rcases hy with rfl | ⟨e1, -⟩
  · exact hp'
  · exact absurd e1 hpt

theorem BFrT.tcbOB (h : BFrT t e σ σ') {p : ObjRef} (hpt : p ≠ t) {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    σ.kheap p = some (.tcb y) := by
  obtain ⟨x, hp', hy⟩ := h.tcbB hp
  rcases hy with rfl | ⟨e1, -⟩
  · exact hp'
  · exact absurd e1 hpt

theorem BFrT.prio (h : BFrT t e σ σ') (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  unfold Sched.prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨y, hk', hy⟩ := h.tcbF hk
      rcases hy with rfl | ⟨-, ep, d, f, rfl⟩
      · rw [hk']
      · rw [hk']; rfl
    | _ =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
        | _ => rfl
  | none =>
    cases hk' : σ'.kheap u with
    | none => rfl
    | some o' => cases o' with
      | tcb y => obtain ⟨x, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
      | _ => rfl

theorem BFrT.nsc {N C : Set U64} (h : BFrT t e σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  exact hN n hn y p (h.ntfnB hy) hp

theorem BFrT.own {T C : Set U64} (h : BFrT t e σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨y, hkt', hsc, -⟩ := h.tcbSc hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc, hsc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      exact hown y n (h.scB hy)
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    exact hun y n (h.scB hy)

theorem BFrT.off (h : BFrT t e σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy; rw [h.sk.csc, h.sk.isc] at ha
  exact hO hc y n (h.scB hy) ha

theorem BFrT.idleOK (h : BFrT t e σ σ') (hO : IdleOK σ) (hti : σ.idleThread ≠ t) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  exact ⟨x, by rw [h.sk.idle]; exact h.tcbO hti hx, by rw [h.sk.isc]; exact h1, h2,
    by rw [h.sk.idle, h.sk.rel]; exact h3⟩

/-- `BlockedScActive` after, `t`'s SCs active. -/
theorem BFrT.bsa (h : BFrT t e σ σ') (hB : BlockedScActive σ)
    (ht : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t → scActive y = true) :
    BlockedScActive σ' := by
  refine ⟨fun p z n u y hp hyt hy hq => ?_, fun p z n hp hr => hB.replies p z n (h.scB hp) hr⟩
  obtain ⟨x, hx, hs⟩ := h.tcbB hy
  rcases hs with rfl | ⟨rfl, -⟩
  · exact hB.tcb p z n u y (h.scB hp) hyt hx hq
  · exact ht p z n (h.scB hp) hyt

/-- `IpcSorted` after, `e`'s queue sorted. -/
theorem BFrT.isorted (h : BFrT t e σ σ') (hS : IpcSorted σ)
    (he : ∀ y, σ'.kheap e = some (.endpoint y) → SortedQ σ y.epQueue) : IpcSorted σ' := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · obtain ⟨x, hx, hc⟩ := h.epB hp
    rcases hc with rfl | rfl
    · exact (hS.1 p y hx).congr fun u _ => h.prio u
    · exact (he y hp).congr fun u _ => h.prio u
  · exact (hS.2 p y (h.ntfnB hp)).congr fun u _ => h.prio u

theorem BFrT.kback (h : BFrT t e σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e' | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e', ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, ep, d, f, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩

theorem BFrT.ksz (h : BFrT t e σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e'⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e'.symm⟩

theorem BFrT.ksub (h : BFrT t e σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e' | ⟨ko, ko', h1, -, -⟩
    · rw [e']; exact hn
    · rw [hn] at h1; cases h1

theorem BFrT.callKeep (h : BFrT t e σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) :=
  ⟨fun q y n hq => ⟨y, h.scF hq, rfl⟩, fun q x hq => ⟨x, h.replyF hq, rfl⟩, fun p x n hp => ⟨x, h.scB hp⟩⟩

theorem BFrT.khrb (h : BFrT t e σ σ') : KhRB σ σ' :=
  KhRB.of_kh h.kh fun p o o' hc => by
    rcases hc with ⟨x, ep, d, f, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ObjRB.tcb (Or.inr rfl)
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)

end

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- The timeout-handler slot of a TCB. -/
theorem tcbSlot4_eq (t : U64) : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 4) = slotOf t 4 := by
  show slotAddr t.bv (Fl4Spec.ofBl _) = _
  rw [slotAddr_ofBl, tcbCnodeIndex_blVal 4 (by decide)]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 64000000 in
/-- **`Running` or `Restart` of an `Inactive` thread other than the current
one, then `handle_timeout` blocking it on its timeout handler's endpoint, at
`J`** (module docstring). -/
theorem JAtZ.runTmoJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : x.tcbTimeoutHandler = .endpointCap p bd r)
    (hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe)
    (ts : Fl4Spec.ThreadState) (hrun : Fl4Spec.runnable ts = true) (hts : tsCode ts < 3) (v : U64)
    (hv : v.val = tsCode ts)
    (hB : sched.set_thread_state st s t v ⦃ s' => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s' ⦄) :
    sched.set_thread_state st s t v ⦃ s6 =>
      XTopAt (L := L) AR Z s6 a (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6
        (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      ∀ b : U64, faults.handle_timeout st arI s6 a t (error.Fault.Timeout b) ⦃ res => ∃ z ∈
        (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv)
          (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv)).1,
        ∃ (V : XVs) (D' : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D' res.1 res.2 z.2 ⦄ ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hta := hP0.e.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR.st
  have hq := IpcRel.not_ep_queued hI.1 (t := t) ⟨by rw [hst, hrs]; decide, by rw [hst, hrs]; decide⟩
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hnq : NotQueued σ t.bv := J.inv.notQueued hk (by rw [hrs]; rfl)
  obtain ⟨y0, n0, hky0, hyt⟩ := J.inv.back t.bv x sc.bv hk hxsc
  rw [hky] at hky0; cases hky0
  have hidt : σ.idleThread ≠ t.bv := by
    intro e
    obtain ⟨y1, h1, -, h3, -⟩ := J.act.2
    rw [e, hk] at h1; cases h1; rw [hrs] at h3; cases h3
  -- the handler cap at the start, its endpoint
  obtain ⟨⟨G0, hB0⟩, -⟩ := hI.2.1
  have hth0 : Z.th t = some .tcb := hB0.tcbT hk
  obtain ⟨xh, cv, hkh, hcv, hca⟩ := hB0.2.1.1.timeoutCap hth0
  rw [hk] at hkh; cases hkh
  have habs := hca.2
  rw [hth] at habs
  obtain ⟨ptr, bdg, sd, rv, g, gr, rfl⟩ : ∃ ptr bdg sd rv g gr, cv = .Endpoint ptr bdg sd rv g gr := by
    cases cv <;> simp [absCap] at habs; exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs
  obtain ⟨hp, hbd, hr⟩ := habs
  subst hp hbd hr
  have hAS : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 4) := ⟨t, rfl, Or.inr ⟨hth0, 4, by decide, rfl⟩⟩
  have hcv' : capAt (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 4)) = ok (.Endpoint ptr bdg sd rv g gr) := by
    rw [tcbSlot4_eq]; exact hcv
  have hpE : ptr ∈ Z.E := J.slotE hAS hcv'
  obtain ⟨xe, hke, -⟩ := hI.1.ep ptr hpE
  have hcbe : Endp.CanBlock false xe := hcb xe hke
  have hpt : ptr.bv ≠ t.bv := fun e => by rw [e, hk] at hke; cases hke
  have hps : ptr.bv ≠ sc.bv := fun e => by rw [e, hky] at hke; cases hke
  -- the endpoint covered by the handler cap
  have hHe : H ptr = some .ep := J.zH.2.1 ptr hpE
  have hfit := J.kern.heap.fits ptr _ hHe
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap (P1.WritesIn.refl s _) hAS.isSlot hcv' (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_ep ptr bdg sd rv g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  -- `set_thread_state`
  refine WP.spec_mono (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) ts hts v hv) (set_thread_state_sfoot hS ht _)) hB) ?_
  rintro s6 ⟨⟨⟨hR6, hS6r⟩, hw6⟩, hblk6, hfoot6⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
  set x6 : Fl4Spec.Tcb := { x with tcbState := ts } with hx6
  set σ1 := updK σ t.bv (.tcb x6) with hσ1
  set σ6 := stsAct σ1 t.bv with hσ6
  have hrec : σ6 = { σ1 with schedulerAction := σ6.schedulerAction } := stsAct_rec σ1 t.bv
  have hk1 : σ1.kheap t.bv = some (.tcb x6) := by simp [hσ1, updK]
  have hk6 : σ6.kheap t.bv = some (.tcb x6) := by rw [hσ6, stsAct_kheap]; exact hk1
  have hkp : ∀ q, q ≠ t.bv → σ6.kheap q = σ.kheap q := by
    intro q hq'; rw [hσ6, stsAct_kheap, hσ1]; simp [updK, hq']
  have e61 : σ6 = σ1 := by
    rw [hσ6]; unfold Notif.stsAct; rw [if_neg]; rintro ⟨h, -⟩; exact htc h
  have e_ct : σ6.curThread = σ.curThread := by rw [hrec]; rfl
  have e_isc : σ6.idleSc = σ.idleSc := by rw [hrec]; rfl
  have hW : P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot (P1.WritesIn.refl _ _) hw6
  have hfx : IpcFree x.tcbState := by
    rw [hrs]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  have hK : ScTKw (fun q => q = t.bv) σ σ6 := by
    refine ⟨fun q => ?_, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl,
      by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, e_ct, e_isc⟩
    by_cases hq' : q = t.bv
    · subst hq'; rw [hk, hk6]
      show TKObj _ _ _
      exact Or.inr (Or.inl ⟨x, x6, rfl, rfl, rfl, Or.inr ⟨rfl, hfx, tsLow_free hts⟩⟩)
    · rw [hkp q hq']; exact OTK.refl _ _
  have hX' : XTopAt (L := L) AR Z s6 a σ6 := xtop_sc_step J.xtop hP0 J.nk hW hK hX6.2.2.1 hX6.1.toN id
  have hks6 : L.ksb s6 = L.ksb s := hW.1
  have hbuf6 : BufWordRel Z.T (L.mem s6) σ6 := J.sc_buf hW hK
  have hI6 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6 σ6 := by
    have h := hX'.irelK (by rw [hks6]; exact J.ks) hbuf6
    have e : σ6.archState = σ.archState := hK.arch
    rw [e] at h; exact h
  refine ⟨hX', hI6, fun b => ?_⟩
  -- the FL4 step from the start to `s6` (`CnStep`)
  have hC1 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ s6 σ6 :=
    ⟨hw6.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot hb)), SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := x6)
      hkp hk6)⟩
  -- `handle_timeout`: the handler cap at `s6`
  obtain ⟨⟨G6, hB6⟩, -⟩ := hI6.2.1
  obtain ⟨xh6, cv6, hkh6, hcv6, hca6⟩ := hB6.2.1.1.timeoutCap (hB6.tcbT hk6)
  rw [hk6] at hkh6; cases hkh6
  have habs6 := hca6.2
  rw [show x6.tcbTimeoutHandler = x.tcbTimeoutHandler from rfl, hth] at habs6
  unfold faults.handle_timeout
  rw [tcb_slot_timeout]
  apply ok_bind_spec
  rw [slot_cap_eq, hcv6]
  apply ok_bind_spec
  cases cv6
  case Endpoint ptr' bdg' sd' rv' g' gr' =>
    simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs6
    obtain ⟨hp', hbd', hr'⟩ := habs6
    obtain rfl : ptr = ptr' := (P1.eq_of_bv hp').symm
    obtain rfl : bdg = bdg' := (P1.eq_of_bv hbd').symm
    have hg : g' = g := by have := congrArg (fun R => decide (Fl4Spec.Rights.allowGrant ∈ R)) hr'; simpa [rights_grant] using this
    have hgr : gr' = gr := by
      have := congrArg (fun R => decide (Fl4Spec.Rights.allowGrantReply ∈ R)) hr'; simpa [rights_grantReply] using this
    obtain rfl : g = g' := hg.symm
    obtain rfl : gr = gr' := hgr.symm
    refine WP.spec_bind (Pₘ := fun r : Bool × S × A => ∃ z ∈ (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv) σ6).1,
      ∃ (V : XVs) (D' : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D' r.2.1 r.2.2 z.2) ?_ ?_
    swap
    · rintro ⟨b0, s2, a2⟩ hr0
      exact (WP.spec_ok _).2 hr0
    unfold faults.send_fault_ipc
    dsimp only
    -- `set_fault`
    set x2 : Fl4Spec.Tcb := { x6 with tcbFault := some (.timeout b.bv) } with hx2
    set σf := updK σ6 t.bv (.tcb x2) with hσf
    refine WP.spec_bind (WP.spec_and (WP.spec_and (set_fault_timeout_top hP0 hI6 ht hk6 b)
      (set_fault_timeout_eq s6 t b)) (WP.spec_and (P1.faults.set_fault.blk (U := ∅) s6 t (error.Fault.Timeout b)
        (t0 := t) hblk6 htH (fun _ h => by simp at h) ?hcb6)
        (P1.faults.set_fault.kw (Cs := Cs) (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
          (Es := P1.EH H) s6 t (error.Fault.Timeout b) hTH htH))) ?_
    case hcb6 =>
      have hS6 : SchedRel st Z.N Z.T Z.C Z.c s6 σ6 := hX6.2.2.1
      obtain ⟨Q, R0, hcq, hs⟩ := hS6.lists
      obtain ⟨x7, hk7, hTR7⟩ := hI6.1.tcb t ht
      rw [hk6] at hk7; cases hk7
      have hv7 : (L.mem s6 (tStA t)).val = tsCode ts := hTR7.st
      have hrr : L.mem s6 (P1.stA t) = sched.TS_RUNNING ∨ L.mem s6 (P1.stA t) = sched.TS_RESTART := by
        have hrr' : ts = .running ∨ ts = .restart := by
          cases ts with
          | running => exact Or.inl rfl
          | restart => exact Or.inr rfl
          | _ => simp [tsCode, Fl4Spec.runnable] at hts hrun
        rcases hrr' with e | e
        · left; apply UScalar.eq_of_val_eq; rw [P1.stA_eq, ← tStA_eq, hv7, e]; unfold sched.TS_RUNNING; rfl
        · right; apply UScalar.eq_of_val_eq; rw [P1.stA_eq, ← tStA_eq, hv7, e]; unfold sched.TS_RESTART; rfl
      have hrq6 : σ6.readyQueues = σ.readyQueues := by rw [hrec]; rfl
      have hrl6 : σ6.releaseQueue = σ.releaseQueue := by rw [hrec]; rfl
      have hac6 : σ6.schedulerAction = σ.schedulerAction := by rw [e61]; rfl
      have hid6 : σ6.idleThread = σ.idleThread := by rw [hrec]; rfl
      obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs.tcb t ht
      rw [hk6] at hkt6; cases hkt6
      have hst6 : L.mem s6 (scA t) = sc := P1.eq_of_bv (Notif.optRef_some (hsct6.symm.trans hxsc)).2
      have h06 : L.mem s6 (scA t) ≠ 0#u64 := (Notif.optRef_some (hsct6.symm.trans hxsc)).1
      have hky6 : σ6.kheap sc.bv = some (.schedContext y n) := by
        rw [hkp _ (fun e => by rw [e, hk] at hky; cases hky)]; exact hky
      obtain ⟨y', n', hky', hy'⟩ := hs.scs sc hsc
      rw [hky6] at hky'; cases hky'
      have hmx : (L.rmax s6 (L.mem s6 (scA t))).val ≠ 0 := by rw [hst6]; exact hy'.rmax_ne hya
      refine ⟨htH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hrr with h | h <;> rw [h]
        · exact P1.not_blocked_running
        · exact P1.not_blocked_restart
      · rcases hrr with h | h <;> rw [h]
        · exact P1.running_ne.1
        · exact P1.restart_ne.1
      · by_contra hq'
        have hm := (hcq.queued t ht).1 hq'
        exact hnq.1 0 _ (by rw [← hrq6, hs.rq _ (hcq.prio t ht), mem_map_bv]; exact hm)
      · by_contra hq'
        have hm := (hcq.released t ht).1 hq'
        exact hnq.2 (by rw [← hrl6, hs.rel, mem_map_bv]; exact hm)
      · refine actionW_ne_of hS6 ht ?_
        rw [hac6]; intro e
        obtain ⟨x', -, -, -, h1, -, h3, -⟩ := schedulable_inv (J.act.1 _ e)
        rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
      · intro h
        have ei : L.idleW s6 = nodeW st s6 Z.c layout.node.IDLE_THREAD := by
          unfold P1.LawfulStore.idleW nodeW; rw [hcq.cur]
        exact hidt (by rw [← hid6, hs.idleTh, ← ei, h])
      · intro hbd
        obtain ⟨⟨Q', R', h0⟩, hBd, hXi, hSc, hSg⟩ := hblk6
        obtain ⟨hiS, -, -⟩ := hXi.2.2.bound _ htH hbd
        exact (hSc.act _ hiS).2 (fun e => hmx (by rw [e]; rfl))
    rintro s7 ⟨⟨⟨hsp7, hI7⟩, hs7⟩, ⟨hblk7, -, hcb7⟩, hfoot7⟩
    have hkf : σf.kheap t.bv = some (.tcb x2) := by simp [hσf, updK]
    have hkfp : ∀ q, q ≠ t.bv → σf.kheap q = σ.kheap q := by
      intro q hq'; rw [hσf]; simp only [updK, Function.update_of_ne hq']; exact hkp q hq'
    have hkef : σf.kheap ptr.bv = some (.endpoint xe) := by rw [hkfp _ hpt]; exact hke
    -- the FL4 step of `set_fault`
    have hC2 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s6 σ6 s7 σf := by
      refine ⟨?_, SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := x2) (fun q hq' => by simp [hσf, updK, hq']) hkf)⟩
      subst hs7
      have w := (((writesIn_wr (st := st) (s := s6) (v := fl4_abi.consts.fault.Timeout) (a_fault hta).1).trans
        (writesIn_wr (v := b) (a_fw0 hta).1)).trans (writesIn_wr (v := 0#u64) (a_fw1 hta).1)).trans
        (writesIn_wr (v := 0#u64) (a_fw2 hta).1)
      refine w.mono fun w0 hw0 => ?_
      have k : ∃ K : Nat, 256 ≤ K ∧ K < 4096 ∧ K ≠ 3440 ∧ K ≠ 3472 ∧ (K ≠ 3512 ∧ K ≠ 3664) ∧ w0.val = t.val + K := by
        rcases hw0 with ((h | h) | h) | h <;> subst h
        · exact ⟨3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩
        · exact ⟨3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩
        · exact ⟨3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩
        · exact ⟨3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩
      obtain ⟨K, k1, k2, k3, k4, k5, k6⟩ := k
      exact Or.inl (Or.inr ⟨t, ht, K, k1, k2, k3, k4, k5, k6⟩)
    -- the spec's blocking send at `σf`
    have hprf : ∀ u, Sched.prioOf σf u = Sched.prioOf σ u := by
      intro u
      by_cases hut : u = t.bv
      · subst hut; exact (prioOf_eq hkf).trans (prioOf_eq hk).symm
      · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq, hkfp u hut]
    have htq : t.bv ∉ xe.epQueue :=
      Endp.not_queued hI.1.toE ht hk ⟨by rw [hrs]; decide, by rw [hrs]; decide⟩ ptr hpE xe hke
    have hqm : ∀ u ∈ xe.epQueue, ∃ z, σf.kheap u = some (.tcb z) := fun u hu => by
      obtain ⟨z, hz, -⟩ := (J.sv.epQ _ _ hke).2 u hu
      exact ⟨z, by rw [hkfp u (fun e => htq (e ▸ hu))]; exact hz⟩
    obtain ⟨σ', heq, F0, hik0, ⟨ds, hkt'⟩, -, hact', -, hsrt⟩ :=
      sendIpcBlock_eq hkf hkef hcbe htq hqm hrun ((J.isorted.1 _ _ hke).congr fun u _ => hprf u)
        false bdg.bv g gr false
    -- FL4's blocking send
    have hIS : IpcSorted σf := by
      have h1 : IpcSorted σ1 := QPK.QPS.sorted (QPK.qps_upd (ko := .tcb x6) hk rfl) J.isorted
      have h2 : IpcSorted σ6 := by rw [e61]; exact h1
      exact QPK.QPS.sorted (QPK.qps_upd (ko := .tcb x2) hk6 rfl) h2
    obtain ⟨⟨Q0, R0, h0⟩, hB0', hX0, hS0, hSg0⟩ := hblk7
    have hst0 : L.epState s7 ptr = 0#u64 ∨ L.epState s7 ptr = 1#u64 := by
      have hx := hI7.1.toE.at_ep hpE hkef
      rw [epState_eq]
      cases xe with
      | idleEP => exact Or.inl hx.1
      | sendEP q => exact Or.inr hx.1
      | recvEP q => simp [Endp.CanBlock] at hcbe
    have hts3 : tsCode ts < 3 := hts
    have hnb : tsCode x2.tcbState ≠ 3 ∧ tsCode x2.tcbState ≠ 4 :=
      ⟨fun h => by have h' : tsCode ts = 3 := h; omega, fun h => by have h' : tsCode ts = 4 := h; omega⟩
    have hnn : ∀ m, x2.tcbState ≠ .blockedOnNotification m := fun m h => by
      have h' : tsCode ts = 6 := congrArg tsCode h
      omega
    have p1f : endpoint.send_ipc st arI s7 a true false bdg g gr false t ptr ⦃ s' _ => P1.Foot st (P1.Heap.tcbs H) Cs
        (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s7 s' ⦄ :=
      P1.endpoint.send_ipc.blockFoot arI s7 a true false bdg g gr false t ptr h0 (fun _ => hcb7) hHe hst0
    refine WP.spec_bind (WP.spec_and (WP.spec_and (send_ipc_blockF (ar := arI) hP0 s7 a σf hI7 ht hkf hnb hnn hpE hkef
      hcbe (Sched.qSorted_of_spec (L := L) hI7.1.toE hI7.1.toN hT hIS ptr (Or.inl hpE)) false bdg g gr false)
      (P1.endpoint.send_ipc.block arI s7 a true false bdg g gr false t ptr Q0 R0 h0 hB0' hX0 hS0 hSg0
        (fun _ => hcb7) hHe hst0))
      p1f) ?_
    rintro ⟨s', a'⟩ ⟨⟨⟨ea, σ0, h0eq, hIR, hW3⟩, hbk⟩, hfoot3⟩
    simp only [WP.uncurry'_pair] at ea hbk hfoot3 hIR hW3
    subst a'
    obtain rfl : σ' = σ0 := by
      have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
      exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
    apply (WP.spec_ok _).2
    -- the spec's outcome
    have hth6 : x6.tcbTimeoutHandler = .endpointCap ptr.bv bdg.bv (rightsOf sd rv g gr) := hth
    have hz : ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv
        (decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr))
        (decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr)) false t.bv ptr.bv
        (updK σ6 t.bv (.tcb { x6 with tcbFault := some (.timeout b.bv) }))).1 := by
      rw [rights_grant, rights_grantReply]
      show ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr false t.bv ptr.bv σf).1
      rw [heq]; exact Set.mem_singleton _
    refine ⟨((), σ'), handleTimeout_mem hk6 hth6 _ hz, ?_⟩
    -- the frame from the start
    have hkt3 : σ'.kheap t.bv =
        some (.tcb { x with tcbState := .blockedOnSend ptr.bv ds, tcbFault := some (.timeout b.bv) }) := hkt'
    have hsk : Sk σ σ' := by
      have h1 : Sk σ σ6 := ⟨e_ct, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl,
        by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, e_isc⟩
      have h2 : Sk σ6 σf := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact (h1.trans h2).trans F0.sk
    have F : BFrT t.bv ptr.bv σ σ' := by
      refine ⟨hsk, fun q => ?_⟩
      by_cases hqt : q = t.bv
      · subst hqt
        exact Or.inr ⟨_, _, hk, hkt3, Or.inl ⟨x, ptr.bv, ds, some (.timeout b.bv), rfl, rfl, rfl⟩⟩
      · rcases F0.kh q with e | ⟨o, o', h1, h2, hc⟩
        · exact Or.inl (e.trans (hkfp q hqt))
        · rw [hkfp q hqt] at h1
          rcases hc with ⟨_, _, _, _, _, e3, -⟩ | ⟨x1, y1, rfl, rfl, e3⟩
          · exact absurd e3 hqt
          · exact Or.inr ⟨_, _, h1, h2, Or.inr ⟨x1, y1, rfl, rfl, e3⟩⟩
    -- the FL4 footprint from the start
    have hC3 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf s' σ' := ⟨hW3, SzKeepC.of F0.szKeep⟩
    have hW : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := ((hC1.trans hC2).trans hC3).1
    have hfoot := P1.Foot.trans (P1.Foot.trans hfoot6 hfoot7) hfoot3
    have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := ⟨⟨Q0, R0, hbk.1⟩, hbk.2⟩
    -- the assembly (as XTopJointSendBlock's `JAtZ.sendBlockJ`)
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
    -- the scheduler action: kept, or a reschedule
    have hact3 : σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread := by
      have e6 : σf.schedulerAction = σ.schedulerAction := by
        show σ6.schedulerAction = σ.schedulerAction; rw [e61]; rfl
      rcases hact' with e | e
      · exact Or.inl (e.trans e6)
      · exact Or.inr e
    have htc' : σ.curThread ≠ t.bv := fun e => htc e.symm
    have hsched : ∀ u, Fl4Spec.schedulable u σ = true → Fl4Spec.schedulable u σ' = true := by
      intro u hs
      obtain ⟨y1, scp, z, n1, hky1, hsc1, hrun1, hkz, hac, hnr⟩ := schedulable_inv hs
      have hut : u ≠ t.bv := by rintro rfl; rw [hk] at hky1; cases hky1; rw [hrs] at hrun1; cases hrun1
      exact schedulable_of (F.tcbO hut hky1) hsc1 hrun1 (F.scF hkz) hac (by rw [F.sk.rel]; exact hnr)
    have hAI3 : ActIdle σ' := by
      refine ⟨fun u hu => ?_, F.idleOK J.act.2 hidt⟩
      have hu0 : σ.schedulerAction = .switchThread u := by
        rcases hact3 with e | e
        · rw [← e]; exact hu
        · rw [e] at hu; cases hu
      exact hsched u (J.act.1 u hu0)
    have hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
      rcases J.cur with e | hC
      · left
        rcases hact3 with e' | e'
        · rw [e', e]
        · exact e'
      · rcases hact3 with e' | e'
        · right
          obtain ⟨xt, hkc, hcs, hnb'⟩ := hC.tcb
          obtain ⟨y1, n1, hk1'⟩ := hC.sc
          refine ⟨⟨xt, by rw [F.sk.ct]; exact F.tcbO htc' hkc, by rw [F.sk.csc]; exact hcs, hnb'⟩,
            ⟨y1, n1, by rw [F.sk.csc]; exact F.scF hk1'⟩, fun hne' y2 n2 hy => ?_, fun hm => ?_⟩
          · rw [F.sk.csc, F.sk.isc] at hne'; rw [F.sk.csc] at hy
            exact hC.active hne' y2 n2 (F.scB hy)
          · rw [F.sk.ct, F.sk.rel] at hm; exact hC.notRel hm
        · exact Or.inl e'
    have hrun3 : CurRunM σ' := by
      by_cases hnr : σ'.schedulerAction ≠ .resumeCurThread
      · exact Or.inl hnr
      have hr' : σ'.schedulerAction = .resumeCurThread := not_not.1 hnr
      have ha : σ'.schedulerAction = σ.schedulerAction := hact3.resolve_right (by rw [hr']; intro e; cases e)
      have h0' : ¬ σ.schedulerAction ≠ .resumeCurThread := fun e => e (by rw [← ha]; exact hr')
      right
      rcases J.curRun.resolve_left h0' with h | h
      · left
        intro y1 hy
        rw [F.sk.ct] at hy
        exact h y1 (F.tcbOB htc' hy)
      · right; rw [F.sk.ct, F.sk.idle]; exact h
    -- the dead: the thread is not dead; the endpoint leaves the dead set
    have hdead : ∀ q ∈ D \ {ptr}, DeadP (L := L) H s' q := fun q hq => by
      have hd := J.jcov.dead q hq.1
      have hqt : q.bv ≠ t.bv := fun h => htD (by rw [← P1.eq_of_bv h]; exact hq.1)
      have hqe : q.bv ≠ ptr.bv := fun h => hq.2 (P1.eq_of_bv h)
      refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ⟨_, F.tcbO hqt hx, rfl, rfl, Or.inl rfl⟩) (fun x hx => ?_)
        (fun x hx => ⟨x, F.ntfnF hx, Or.inl rfl, rfl, Or.inl rfl⟩)
        (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
        (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1 (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
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
    -- `Inv` (`InvBut.ik`; the thread a sender with a timeout fault, `inClassR`)
    have hsp : Fl4Spec.setThreadState (Z := Unit) t.bv ts σ = ({((), σ6)}, False) := Notif.setThreadState_eq ts hk
    have hts6 : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some (.timeout b.bv) }) t.bv σ6 =
        ({((), σf)}, False) := Notif.threadSet_eq _ hk6
    have hik : IK t.bv σ σ' :=
      (((ikm_setThreadState ts).of_eq hsp).trans ((ikm_threadSet (t := t.bv) (p := t.bv)
        (g := fun tcb => { tcb with tcbFault := some (.timeout b.bv) })
        fun _ => ⟨rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩).of_eq hts6)).trans hik0
    obtain ⟨hIB, -⟩ := (J.inv.toBut t.bv).ik hnq hik
    have I3 : Inv σ' := hIB.inv fun x' hx' hc => by
      rw [hkt3] at hx'; cases hx'
      exact (inClassR.notTmoS hc ptr.bv ds b.bv rfl rfl).elim
    -- `BlockedScActive`: the thread's SC is `sc`, active
    have hscA : ∀ q y1 n1, σ.kheap q = some (.schedContext y1 n1) → y1.scTcb = some t.bv →
        Fl4Spec.scActive y1 = true := by
      intro q y1 n1 hq' hyt'
      obtain ⟨c, hcC, eq⟩ := J.obj.sc q y1 n1 hq'
      subst eq
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hc0 := J.c0 c hcC
      have hcS : c ∈ P1.Heap.scs H := ⟨_, (hJ.sc c y1 n1 hc0 hq').2⟩
      obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hcC hcS hc0 hq' hyt'
      rw [hk] at hku; cases hku
      have e1 : c.bv = sc.bv := Option.some.inj (hxs.symm.trans hxsc)
      rw [e1, hky] at hq'; cases hq'
      exact hya
    have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {ptr}) s' σ' :=
      ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
        J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
        J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
        hAI3, F.bsa J.bsa hscA, F.isorted J.isorted fun y1 hy1 => (hsrt y1 hy1).congr fun u _ => (hprf u).symm,
        hrun3, hblk⟩
    have hC0 := JCs.same J hF.1 F.ksz
    have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
    exact ⟨Z.vs, D \ {ptr}, J.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hCs R hKd F.sk.orig hidl.1 (J.zD_diffE hpE)⟩
  all_goals simp [absCap] at habs6

end

end

end Fl4Proofs.P3
