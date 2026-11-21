/-
P3 (DESIGN.md §9): **the primitive steps of the decodes, for the composite
relation** (TopXAll's `XTop`). A decode's post records that its run is a
composition of primitive steps by `StepClosed`: every relation `Q` closed
under the current thread's restart (`restart`), a kernel-state step (`ks`:
`KsW` words, the spec's `KsStep`, the domain words kept, the IRQ and IO-port
relations kept, an arch operation of the interrupt or IO port decodes, `ArchIrqStep`) and a capability
insert into a CNode (`slot`, with the CSpace relation after), a CNode-only
step (`cslot`: the spec's `CnK` changing CNodes only, FL4's slot words, the
CSpace relation after: a move, a swap), a scheduler
step (`sched`: `SchedStep`, the queue, action and domain-schedule words and
the scheduler relation after at every family of sets) relates its start and
end. A notification cap's deletion (`delete_one`, the IRQ handler
invocations) is no primitive step: IrqHandler's `IrqSteps` records it beside
the steps, and each relation proves it with its own invariant (XTopIrqH at
`XTop`, XTopJointIrqL at `J` with the entry's `LiveJ`). XTopStep
proves `XTop`'s instance; the decodes stay free of the composite relation's
definitions.
-/
import Fl4Proofs.P3.DomKeep
import Fl4Proofs.P3.IoBitmap
import Fl4Proofs.P3.MdbStepVs
import Fl4Proofs.P3.CnodeRevoke
import Fl4Proofs.P3.VsInsFrame
import Fl4Proofs.P3.SchedRel
import Fl4Proofs.P3.SpecCnK
import Fl4Proofs.P3.SlotCover
import Fl4Proofs.P1.QueueBlock
import Fl4Proofs.P3.VsCapWBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The kernel-global words a kernel-state step may write: past the current
domain and domain time words, not the kernel root, not the IRQ node's CTEs
(`ksb + 1248 .. ksb + 5344`, written by slot steps only). -/
def KsW (kb b : U64) : Prop := ∃ K : U64, 24 ≤ K.val ∧ K.val < 13568 ∧ K.val ≠ 48 ∧ b.val = kb.val + K.val ∧
  (K.val < 1248 ∨ 5344 ≤ K.val)

/-- The spec's kernel-state steps: only the interrupt states, the IRQ masks,
the IO ports, the arch IRQ states and the domain schedule change. -/
structure KsStep (σ σ' : Fl4Spec.State Unit) : Prop where
  kh : σ'.kheap = σ.kheap
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  rq : σ'.readyQueues = σ.readyQueues
  rel : σ'.releaseQueue = σ.releaseQueue
  ct : σ'.curThread = σ.curThread
  act : σ'.schedulerAction = σ.schedulerAction
  csc : σ'.curSc = σ.curSc
  ctime : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  repr : σ'.reprogramTimer = σ.reprogramTimer
  cdom : σ'.curDomain = σ.curDomain
  dtime : σ'.domainTime = σ.domainTime
  idle : σ'.idleThread = σ.idleThread
  isc : σ'.idleSc = σ.idleSc
  inode : σ'.interruptIrqNode = σ.interruptIrqNode
  um : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory
  asidT : σ'.archState.x64AsidTable = σ.archState.x64AsidTable
  gpml4 : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4
  cr3 : σ'.archState.x64CurrentCr3 = σ.archState.x64CurrentCr3

theorem KsStep.refl (σ : Fl4Spec.State Unit) : KsStep σ σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A word of a slot of the typed heap. -/
def InSlot (th : TypedHeap) (b : U64) : Prop := ∃ a, IsSlot th a ∧ a.val ≤ b.val ∧ b.val < a.val + 32

/-- The spec's scheduler steps: only the ready queues, the scheduler
action, the domain time and index and the domain schedule's start change. -/
structure SchedK (σ σ' : Fl4Spec.State Unit) : Prop where
  kh : σ'.kheap = σ.kheap
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  rel : σ'.releaseQueue = σ.releaseQueue
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  ctime : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  repr : σ'.reprogramTimer = σ.reprogramTimer
  cdom : σ'.curDomain = σ.curDomain
  idle : σ'.idleThread = σ.idleThread
  isc : σ'.idleSc = σ.idleSc
  inode : σ'.interruptIrqNode = σ.interruptIrqNode
  ist : σ'.interruptStates = σ.interruptStates
  ms : σ'.machineState = σ.machineState
  arch : σ'.archState = σ.archState

theorem SchedK.refl (σ : Fl4Spec.State Unit) : SchedK σ σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SchedK.trans {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : SchedK σ1 σ2) (h2 : SchedK σ2 σ3) : SchedK σ1 σ3 :=
  ⟨h2.kh.trans h1.kh, h2.cdt.trans h1.cdt, h2.orig.trans h1.orig, h2.rel.trans h1.rel, h2.ct.trans h1.ct,
    h2.csc.trans h1.csc, h2.ctime.trans h1.ctime, h2.cons.trans h1.cons, h2.repr.trans h1.repr,
    h2.cdom.trans h1.cdom, h2.idle.trans h1.idle, h2.isc.trans h1.isc, h2.inode.trans h1.inode, h2.ist.trans h1.ist,
    h2.ms.trans h1.ms, h2.arch.trans h1.arch⟩

/-- **The domain schedule relation** as DomDecode states it (`DomRel`,
`domRel_iff`), for the steps' statements: the table's domain and duration
words are the spec's `domain_list` (2 entries), and the start word its
`domain_start_index`. -/
def DomRelW (m : U64 → U64) (kb : U64) (σ : Fl4Spec.State Unit) : Prop :=
  σ.domainList.length = 2 ∧
  (∀ i : U64, i.val < 2 →
    σ.domainList[i.val]? = some
      (BitVec.ofNat 8 (m (core.num.U64.wrapping_add kb
        (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)))).val,
       BitVec.ofNat 56 (m (core.num.U64.wrapping_add kb (core.num.U64.wrapping_add
        (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)) 8#u64))).val) ∧
    (m (core.num.U64.wrapping_add kb
      (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)))).val < 2 ^ 8 ∧
    (m (core.num.U64.wrapping_add kb (core.num.U64.wrapping_add
      (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)) 8#u64))).val < 2 ^ 56 ∧
    (m (core.num.U64.wrapping_add kb (core.num.U64.wrapping_add
      (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)) 8#u64)) = 0#u64 →
      m (core.num.U64.wrapping_add kb
        (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64))) = 0#u64)) ∧
  σ.domainStartIndex = (m (core.num.U64.wrapping_add kb 32#u64)).val

/-- Every object of `σ'` was an object of the same type in `σ` (SpecKSz). -/
def KSz (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.aType ko = Fl4Spec.aType ko'

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The arch operations of the interrupt and IO port decodes: none, an
IRQ's mask, an IOAPIC pin's (remapped) programming, a port access. -/
def ArchIrqStep (a a' : A) : Prop :=
  a' = a ∨ (∃ irq b, arI.mask_irq a irq b = ok a') ∨
    (∃ i p l po v b, arI.ioapic_map a i p l po v = ok (b, a')) ∨
    (∃ i p l po v h b, arI.ioapic_map_remapped a i p l po v h = ok (b, a')) ∨
    (∃ p z v, arI.port_in a p z = ok (v, a')) ∨ (∃ p z d, arI.port_out a p z d = ok a') ∨
    (∃ irq, arI.irq_free a irq = ok a')

/-- The kernel-global words of the domain schedule a scheduler step may
write: the domain time and index, the start and the table. -/
def DomKW (kb b : U64) : Prop := ∃ K ∈ ([16, 24, 32, 192, 200, 208, 216] : List Nat), b.val = kb.val + K

theorem domKW_val {kb b : U64} (h : DomKW kb b) :
    kb.val + 16 ≤ b.val ∧ b.val ≤ kb.val + 216 ∧ b.val ≠ kb.val + 8 ∧ b.val ≠ kb.val + 48 := by
  obtain ⟨K, hK, e⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
  omega

/-- The words a scheduler step writes: the `Sched` links and `IN_QUEUES`
word of the TCBs of `T`, core `c`'s node, and the domain time, domain index
and domain-schedule words (start, table). -/
def SchW (T : Set U64) (c : U64) (s : S) (b : U64) : Prop :=
  (∃ y ∈ T, b = core.num.U64.wrapping_add y 3480#u64 ∨ b = core.num.U64.wrapping_add y 3488#u64 ∨
    b = core.num.U64.wrapping_add y 3592#u64) ∨
  (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288 ∧ b.val ≠ L.nodeBase s c + 88) ∨ DomKW (L.ksb s) b

/-- **A scheduler step's ready queues and action**: every member of a ready
queue after was a member before or was schedulable; the action is kept or
becomes `chooseNewThread`. -/
def SchedQOK (σ σ' : Fl4Spec.State Unit) : Prop :=
  (∀ d p u, u ∈ σ'.readyQueues d p → (∃ d' p', u ∈ σ.readyQueues d' p') ∨ Fl4Spec.schedulable u σ = true) ∧
  (σ'.schedulerAction = .chooseNewThread ∨ σ'.schedulerAction = σ.schedulerAction)

theorem SchedQOK.refl (σ : Fl4Spec.State Unit) : SchedQOK σ σ :=
  ⟨fun d p _ hu => Or.inl ⟨d, p, hu⟩, Or.inr rfl⟩

/-- **P1's `BlkOK` kept**, at every family of sets whose TCBs include the
typed heap's. -/
def BlkKeep (th : TypedHeap) (s s' : S) : Prop :=
  ∀ (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64),
    (∀ t, th t = some .tcb → t ∈ T) → P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s'

/-- **A scheduler step** (`set_domain`, `reschedule_required`, the domain
schedule's start and configuration): the spec changes only the scheduler's
fields (`SchedK`); at every family of sets whose TCBs include the typed
heap's, from the scheduler and notification relations, FL4 writes only
`SchW` words and the scheduler relation holds after; the domain relation is
kept; the ready queues gain only schedulable threads (`SchedQOK`) and P1's
`BlkOK` is kept (`BlkKeep`). -/
def SchedStep (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (s' : S) (σ' : Fl4Spec.State Unit) : Prop :=
  SchedK σ σ' ∧ (∀ (N T C : Set U64) (c : U64), (∀ t, th t = some .tcb → t ∈ T) →
    Sched.SchedRel st N T C c s σ → Notif.NtfnStateRel N T (L.mem s) σ →
    Sched.SchedRel st N T C c s' σ' ∧ P1.WritesIn st s s' (SchW (L := L) T c s) ∧
    (DomRelW (L.mem s) (L.ksb s) σ → DomRelW (L.mem s') (L.ksb s) σ')) ∧
    SchedQOK σ σ' ∧ BlkKeep (st := st) th s s'

/-- The current thread runnable (what the restart needs). -/
def CurRun (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true

/-- **`CurRun` or the idle thread current** (l4v `ct_running or ct_idle`):
what holds at every kernel exit (`schedule` may choose the idle thread,
whose state is not runnable). A system call enters from a thread, not the
idle one, so `CurRun` holds again at its decode (`CurRunW.run`). -/
def CurRunW (σ : Fl4Spec.State Unit) : Prop :=
  CurRun σ ∨ σ.curThread = σ.idleThread

theorem CurRunW.run {σ : Fl4Spec.State Unit} (h : CurRunW σ) (hni : σ.curThread ≠ σ.idleThread) : CurRun σ :=
  Or.resolve_right h hni

/-- **A system call's entry state** (l4v `ct_running` and
`scheduler_action = resume_cur_thread` at kernel entry): not the idle
thread, the action `resumeCurThread` (`schedule` ends in it). -/
def Entered (σ : Fl4Spec.State Unit) : Prop :=
  σ.curThread ≠ σ.idleThread ∧ σ.schedulerAction = .resumeCurThread

/-- **`CurRunW` unless a reschedule or switch is pending** (`JAtZ.curRun`,
mid-entry: a blocking step leaves the current thread blocked with
`chooseNewThread`; a revoke that first wakes a thread (`switchThread`) and
then finalises the current thread's TCB leaves it `Inactive` with the switch
pending, `set_thread_state` turning only `resumeCurThread` into
`chooseNewThread`; l4v's `ct_in_state` is likewise only required while the
current thread is resumed). `schedule` re-establishes `CurRunW`: it keeps the
current thread only when resumed. -/
def CurRunM (σ : Fl4Spec.State Unit) : Prop :=
  σ.schedulerAction ≠ .resumeCurThread ∨ CurRunW σ

theorem CurRunM.run {σ : Fl4Spec.State Unit} (h : CurRunM σ) (hni : Entered σ) : CurRun σ :=
  (h.resolve_left fun e => e hni.2).run hni.1

/-- A pending reschedule is no resumption. -/
theorem act_cn_nr {a : Fl4Spec.SchedulerAction} (e : a = .chooseNewThread) : a ≠ .resumeCurThread := by
  rw [e]; intro h; cases h

/-- `CurRunM` after a step that keeps `CurRunW` and resumes nothing newly. -/
theorem CurRunM.of_act {σ σ' : Fl4Spec.State Unit} (hR : CurRunM σ) (hW : CurRunW σ → CurRunW σ')
    (ha : σ.schedulerAction ≠ .resumeCurThread → σ'.schedulerAction ≠ .resumeCurThread) : CurRunM σ' :=
  hR.imp ha hW

/-- `CurRunM` after a step that keeps `CurRunW` and keeps the action or
requests a reschedule. -/
theorem CurRunM.of_cn {σ σ' : Fl4Spec.State Unit} (hR : CurRunM σ) (hW : CurRunW σ → CurRunW σ')
    (ha : σ'.schedulerAction = .chooseNewThread ∨ σ'.schedulerAction = σ.schedulerAction) : CurRunM σ' :=
  hR.of_act hW fun e => ha.elim act_cn_nr fun e' => by rw [e']; exact e

/-- **Closure under the primitive steps** (module docstring). -/
structure StepClosed (th : TypedHeap) (Q : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop) :
    Prop where
  trans : ∀ s1 a1 σ1 s2 a2 σ2 s3 a3 σ3, Q s1 a1 σ1 s2 a2 σ2 → Q s2 a2 σ2 s3 a3 σ3 → Q s1 a1 σ1 s3 a3 σ3
  restart : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (ct : U64) (x : Fl4Spec.Tcb) (s1 : S),
    σ.curThread = ct.bv → σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    Fl4Spec.runnable x.tcbState = true → sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Q s a σ s1 a (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)
  ks : ∀ (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit), P1.WritesIn st s s' (KsW (L.ksb s)) → KsStep σ σ' →
    DK4 (L := L) s s' → σ'.domainList = σ.domainList → σ'.domainStartIndex = σ.domainStartIndex →
    (IrqRel (L.mem s) (L.ksb s) σ → IrqRel (L.mem s') (L.ksb s) σ') →
    (IoRel (L.mem s) (L.ksb s) σ → IoRel (L.mem s') (L.ksb s) σ') →
    ArchIrqStep arI a a' → Q s a σ s' a' σ'
  slot : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G' : MdbGhost) (c : Fl4Spec.Cap) (ps pd : U64)
    (rs rd : Nat) (idxs idxd : List Bool), th ps = some (.cnode rs) → th pd = some (.cnode rd) →
    Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) →
    idxd.length = rd → (∀ y, IsSlot th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y) →
    capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null →
    (∀ p sb fi d, capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Untyped p sb fi d) →
    P1.WritesIn st s s' (InSlot th) → CRel th (L.mem s') σ' G' → FinInv th (L.mem s') σ' G' →
    MdbOKV (L.ksb s) (L.mem s') G' →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1)) →
    TypedKept th (L.mem s) (L.mem s') →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3)) →
    DestLive th (L.mem s) (L.ksb s) pd →
    (DelInv th (L.mem s) → DelInv th (L.mem s')) → Vs.VsSlotsT th (L.mem s) (L.mem s') →
    capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Null →
    (∀ p zt n, capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Zombie p zt n) → Q s a σ s' a σ'
  sched : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit), SchedStep (L := L) th s σ s' σ' → Q s a σ s' a σ'
  cslot : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G' : MdbGhost), Ipc.CnK σ σ' →
    (∀ p, σ'.kheap p = σ.kheap p ∨
      ∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) →
    CoverKept th (L.mem s) (L.mem s') → UtKept th (L.mem s) (L.mem s') →
    (∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot th sl) →
    P1.WritesIn st s s' (InSlot th) → CRel th (L.mem s') σ' G' → FinInv th (L.mem s') σ' G' →
    MdbOKV (L.ksb s) (L.mem s') G' →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1)) →
    TypedKept th (L.mem s) (L.mem s') →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3)) →
    KSz σ σ' → (DelInv th (L.mem s) → DelInv th (L.mem s')) → ∀ W : List Fl4Spec.CslotPtr,
    (∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ th p = some (.cnode r) ∧ sl.2.length = r ∧ DestLive th (L.mem s) (L.ksb s) p) →
    (∀ y, IsSlot th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s) y) →
    (∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ W) →
    UtSrc th (L.mem s) (L.mem s') σ σ' → Vs.VsSlotsT th (L.mem s) (L.mem s') →
    CnLive (L.mem s) (L.mem s') W →
    (∀ sl ∈ W, capV (L.mem s') (cslotAddr sl) = .Null → σ'.isOriginalCap sl = false) → Q s a σ s' a σ'

/-- **A run made of primitive steps** (module docstring). -/
def Steps (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) :
    Prop :=
  ∀ Q, StepClosed (L := L) arI th Q → Q s a σ s' a' σ'

theorem Steps.trans {th : TypedHeap} {s1 s2 s3 : S} {a1 a2 a3 : A} {σ1 σ2 σ3 : Fl4Spec.State Unit}
    (h1 : Steps (L := L) arI th s1 a1 σ1 s2 a2 σ2) (h2 : Steps (L := L) arI th s2 a2 σ2 s3 a3 σ3) :
    Steps (L := L) arI th s1 a1 σ1 s3 a3 σ3 :=
  fun Q hQ => hQ.trans _ _ _ _ _ _ _ _ _ (h1 Q hQ) (h2 Q hQ)

/-- **A scheduler step** (`StepClosed.sched`). -/
theorem Steps.sched {th : TypedHeap} {s s' : S} {a : A} {σ σ' : Fl4Spec.State Unit}
    (h : SchedStep (L := L) th s σ s' σ') : Steps (L := L) arI th s a σ s' a σ' :=
  fun _ hQ => hQ.sched s s' a σ σ' h

end


/-! ## The steps of the decodes -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem spec_self {α : Type} {p : Result α} {P : α → Prop} (h : p ⦃ P ⦄) : p ⦃ fun x => p = ok x ⦄ := by
  obtain ⟨x, hx, -⟩ := spec_exists h
  rw [hx]; exact (WP.spec_ok _).2 rfl

/-- The current thread's restart (`StepClosed.restart`), from the spec's
single outcome. -/
theorem Steps.restart {th : TypedHeap} {s s1 : S} {a : A} {σ σ1 : Fl4Spec.State Unit} {ct : U64}
    {x : Fl4Spec.Tcb} (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x)) (htcb : th ct = some .tcb)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hC : CurRun σ) :
    Steps (L := L) arI th s a σ s1 a σ1 := by
  intro Q hQ
  have hrun : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  exact hQ.restart s a σ ct x s1 hcur hk htcb hrun hs1

theorem IoRel.irqWr {th : TypedHeap} {kb : U64} (hL : IntLayout th kb) {s : S} {σ : Fl4Spec.State Unit}
    (hR : IoRel (L.mem s) kb σ) {i : U64} (hi : i.val < 128) (v : U64) (σ' : Fl4Spec.State Unit)
    (hio : σ'.archState.x64AllocatedIoPorts = σ.archState.x64AllocatedIoPorts) :
    IoRel (L.mem (L.wr s (irqStA kb i) v)) kb σ' := by
  intro p hp
  have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
  have hv := ioA_val hL.fit hw
  have hv2 := irqStA_val hL.fit hi
  have ha := hL.align
  unfold bitOf
  rw [hio, L.mem_wr_ne (by unfold P1.Aligned; rw [hv2]; omega) (by unfold P1.Aligned; rw [hv]; omega)
    (by rw [hv, hv2]; omega)]
  exact hR p hp

/-- **An IRQ state word's write** (`StepClosed.ks`), with the arch state's
mask. -/
theorem Steps.irqWr {th : TypedHeap} {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} (hL : IntLayout th (L.ksb s))
    {irq : U64} (hirq : irq.val < 128) (v : U64) {b : Bool} (hm : arI.mask_irq a irq b = ok a1)
    (sti : Fl4Spec.IrqState) (hsti : irqSt v = sti) :
    Steps (L := L) arI th s a σ (L.wr s (irqStA (L.ksb s) irq) v) a1 (setIrqSt sti (BitVec.ofNat 8 irq.val) σ) := by
  intro Q hQ
  have hv := irqStA_val hL.fit hirq
  have ha8 : (L.ksb s).val % 8 = 0 := by have := hL.align; omega
  refine hQ.ks _ _ _ _ _ _ ((P1.writesIn_wr (by unfold P1.Aligned; rw [hv]; omega)).mono fun b e => ?_)
    (by constructor <;> rfl) (DK4.irqSt hL.fit ha8 hirq v) rfl rfl
    (fun h => IrqRel.wr hL h hirq v _ (by rw [← hsti]; rfl) rfl) (fun h => IoRel.irqWr hL h hirq v _ rfl)
    (Or.inr (Or.inl ⟨irq, b, hm⟩))
  subst e
  have hK : (⟨BitVec.ofNat 64 (224 + 8 * irq.val)⟩ : U64).val = 224 + 8 * irq.val := by
    show (BitVec.ofNat 64 _).toNat = _; simp; omega
  exact ⟨⟨BitVec.ofNat 64 (224 + 8 * irq.val)⟩, by rw [hK]; omega, by rw [hK]; omega, by rw [hK]; omega,
    by rw [hK, hv]; omega, by rw [hK]; omega⟩

/-- **A spec-only kernel-state step** (an arch IRQ state, say). -/
theorem Steps.ksSpec {th : TypedHeap} {s : S} {a : A} {σ σ' : Fl4Spec.State Unit} (hO : KsStep σ σ')
    (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex)
    (hirq : IrqRel (L.mem s) (L.ksb s) σ → IrqRel (L.mem s) (L.ksb s) σ')
    (hio : IoRel (L.mem s) (L.ksb s) σ → IoRel (L.mem s) (L.ksb s) σ') :
    Steps (L := L) arI th s a σ s a σ' := fun Q hQ =>
  hQ.ks s s a a σ σ' (P1.WritesIn.refl _ _) hO (DK4.refl s) hdl hds hirq hio (Or.inl rfl)

/-- **An arch operation of an interrupt decode.** -/
theorem Steps.arch {th : TypedHeap} {s : S} {a a' : A} {σ : Fl4Spec.State Unit} (h : ArchIrqStep arI a a') :
    Steps (L := L) arI th s a σ s a' σ := fun Q hQ =>
  hQ.ks s s a a' σ σ (P1.WritesIn.refl _ _) (KsStep.refl σ) (DK4.refl s) rfl rfl id id h

/-- **A capability insert into a CNode slot** (`StepClosed.slot`), from the
insert's frame (`insert_frame2`) and the CSpace relation after. -/
theorem Steps.insert {th : TypedHeap} (hP : Placed th) {s s' : S} {a : A} {σ σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {c : Fl4Spec.Cap} {ps pd : U64} {rs rd : Nat} {idxs idxd : List Bool} (hps : th ps = some (.cnode rs))
    (hpd : th pd = some (.cnode rd)) (hld : idxd.length = rd)
    (hci : Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False))
    (hF : Vs.SlotFrame2 (L := L) th s s') (hCR : CRel th (L.mem s') σ' G') (hFI : FinInv th (L.mem s') σ' G')
    (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hcap : ∀ y, IsSlot th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y)
    (hnull : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (hnu : ∀ p sb fi d, capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Untyped p sb fi d)
    (hTK : TypedKept th (L.mem s) (L.mem s')) (hDL : DestLive th (L.mem s) (L.ksb s) pd)
    (hDl : DelInv th (L.mem s) → DelInv th (L.mem s'))
    (hvt : ∀ P L4 L3 L2 L1 : Set U64, Vs.VsSlotsW th P L4 L3 L2 L1 (L.mem s) →
      Vs.VCapW P L4 L3 L2 L1 (capV (L.mem s') (cslotAddr (pd.bv, idxd))))
    (hft : ∀ U : Nat → Prop, Vs.FrSlots th U (L.mem s) → Vs.FrIn U (capV (L.mem s') (cslotAddr (pd.bv, idxd))))
    (hnt : Vs.VsNat th (L.mem s) → Vs.NativeCap (capV (L.mem s') (cslotAddr (pd.bv, idxd))))
    (hnn : capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Null)
    (hnz : ∀ p zt n, capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Zombie p zt n) :
    Steps (L := L) arI th s a σ s' a σ' := by
  intro Q hQ
  refine hQ.slot s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu
    ⟨hF.1, hF.2.1, fun b hb hn => hF.2.2 b hb fun ⟨x, k, hx, hk, e⟩ => hn ⟨x, hx, ?_⟩⟩ hCR hFI hMO (fun t ht => ?_) hTK (fun t ht => ?_) hDL hDl
    (Vs.VsSlotsT.of_some (· = cslotAddr (pd.bv, idxd)) (fun y hy hn => hcap y hy hn) (fun y _ e => by subst e; exact hvt) (fun y _ e => by subst e; exact hft) fun y _ e => by subst e; exact hnt) hnn hnz
  · have hf := hx.fit hP
    have := hk.lt
    have hv := wordOf_val (a := x) (k := k) (by omega)
    rw [e, hv]; omega
  · have h1 : IsSlot th (slotOf t 1) := ⟨t, 1, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hne : slotOf t 1 ≠ cslotAddr (pd.bv, idxd) := by
      intro e
      obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := th) (sl := (pd.bv, idxd)) ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
      have hpp : p = pd := P1.eq_of_bv hp1.symm
      subst hpp
      have := IsSlotAt.apart hP (Or.inr ⟨ht, by decide⟩ : IsSlotAt th t 1) hi (fun hh => by
        obtain ⟨h, -⟩ := hh; subst h; rw [hpd] at ht; cases ht)
      rw [e, hp2] at this; omega
    rw [capAt_capV, capAt_capV, hcap _ h1 hne]
  · have h1 : IsSlot th (slotOf t 3) := ⟨t, 3, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hne : slotOf t 3 ≠ cslotAddr (pd.bv, idxd) := by
      intro e
      obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := th) (sl := (pd.bv, idxd)) ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
      have hpp : p = pd := P1.eq_of_bv hp1.symm
      subst hpp
      have := IsSlotAt.apart hP (Or.inr ⟨ht, by decide⟩ : IsSlotAt th t 3) hi (fun hh => by
        obtain ⟨h, -⟩ := hh; subst h; rw [hpd] at ht; cases ht)
      rw [e, hp2] at this; omega
    rw [capAt_capV, capAt_capV, hcap _ h1 hne]

end

end

end Fl4Proofs.P3
