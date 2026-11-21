/-
P3 (DESIGN.md §9), invariant line g5b (KENTRY-PLAN g5b; g5a's handoff, INV-PLAN
§1.3 E8 / E9 / E17, P1): **`kernel_entryJ36E`** = `kernel_entryJ37` (the `MR`
carry of g4b) with `kernel_entryJ35E`'s reduced dispatch bundle, and the
induction `JReachI` / `jreach_invI` / `kernel_entry_reachI` over
`JAtZ ∧ SInvX ∧ SInvIR ∧ MR`.

Two of g5a's four spec-only entry facts (`SInvI`) are no longer asked:
* `SpecIrqH` (the IRQ handler caps' lines valid and not inactive): the bound
  `irq ≤ maxIRQ` was never needed (FL4's `CapValid` of an IRQ handler cap
  already bounds the line below 128, `handlersActive_of_vih`), and the rest
  is l4v `valid_irq_handlers`, already carried in `SInvX` (`SInvA.vih`, vih3's
  `kentry_validIrqMasks`). So `HandlersActive` is a theorem of `JAtZ` and
  `SInvX` (`JAtZ.handlersJV`).
* `SpecFrPg` (ReadFPU's destination frame in one spec data page): g5b
  restated XTopJointReadFpu's `FpuFrameJHyp` per byte (`UFr`), which is
  `JAtZ.fcap` at the slot (`JAtZ.fpuFrameJ`, no spec fact).
`flags` (`FlagsRel`, FL4's flags words vs the spec's `tcb_flags`) leaves the
dispatch bundle: asked at the entry state and carried to the dispatch state
(`flags_front`; `KDispHypsKV36E`, `JEntryAtR6`).
The Frame path's `hno` (`JFramePath`) likewise: `LargeFrOK` (every MDB
slot's large non-device frame cap against every MDB cap) at the entry state,
kept by the front (`front_slotsSame`, `LargeFrOK.of_same`), gives it at the
invoked slot (`JPathAtM36E.to35E`).
Left: **`SInvIR σ`** = `SpecIoP σ ∧ SpecUtZ σ` (l4v `valid_ioports`,
`untyped_ranges_zero`) [J] spec, asked at the entry and carried to the
dispatch state (`sinvIR_disp`). Their carry across a whole syscall is NOT
proved (KENTRY-PLAN g5b): `JReachI.step` asks `SInvIR` of the exit state
(the one open carry of this induction, like g4a's `MR` before g4b).
-/
import Fl4Proofs.P3.XTopJointKEntry37
import Fl4Proofs.P3.XTopJointKEntry35E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **[J] FL4 (l4v `valid_cap` / the frame-cap overlap discipline,
INV-PLAN P8; `JFramePath.hno` for every MDB slot at once)**: every MDB slot's
large non-device frame cap is, against every MDB slot's cap, disjoint from
it, or that cap is a non-revocable frame cap, or it lies within that cap.
A statement about the state alone (no invocation): asked at the entry state
and carried to the dispatch state (`largeFr_front`). -/
def LargeFrOK (G : MdbGhost) (m : U64 → U64) : Prop :=
  ∀ y ∈ G.chains.flatten, ∀ (p rt : U64) (mp : Bool) (asid va : U64),
    capV m y = .Frame p .Large rt false mp false asid va → ∀ x ∈ G.chains.flatten,
      Disj (capV m x) (.Frame p .Large rt false mp false asid va) ∨
      (isFrame (capV m x) = true ∧ revOf m x = false) ∨
      Within (.Frame p .Large rt false mp false asid va) (capV m x)

/-- `LargeFrOK` across a step keeping every slot of the typed heap. -/
theorem LargeFrOK.of_same {th : TypedHeap} {G : MdbGhost} {m m' : U64 → U64} (h : LargeFrOK G m)
    (hG : ∀ y ∈ G.chains.flatten, IsSlot th y) (hS : SlotsSame th m m') : LargeFrOK G m' := by
  intro y hy p rt mp asid va hc x hx
  have ex := hS.capV (hG x hx)
  have ey := hS.capV (hG y hy)
  have er : revOf m' x = revOf m x := by unfold revOf; rw [(hS x (hG x hx)).2.2.2]
  rw [ex, er]
  exact h y hy p rt mp asid va (by rw [← ey]; exact hc) x hx

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {th : TypedHeap}

/-- **`HandlersActive` from l4v's `valid_irq_handlers` alone** (no `maxIRQ`
bound: FL4's `CapValid` of a handler cap gives the line below 128). -/
theorem handlersActive_of_vih {s : S} {kb : U64} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hR : StateRel th (L.mem s) σ) (hM : MdbLinks th (L.mem s) G) (hIR : IrqRel (L.mem s) kb σ)
    (hV : SInvV.ValidIrqHandlers σ) : HandlersActive (L.mem s) kb G := by
  intro y hy i hi
  obtain ⟨ysl, hys, rfl⟩ := ((hM.members _).1 hy).1.abs
  obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hys
  rw [capV_of_capAt hc] at hi; subst hi
  have h128 : i.val < 128 := hca.1
  rw [hca.abs] at hg
  obtain ⟨-, hco⟩ := SInvV.vih_mem_getCap (o := ysl.1) (c := ysl.2) (x := (_, σ))
    (by rw [hg]; exact Set.mem_singleton _)
  have h2 := hV _ _ _ hco
  refine ⟨h128, fun h0 => h2 ?_⟩
  rw [hIR.st i h128, (irqSt_inactive _).2 h0]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **`HandlersActive` at `J` from `SInvX`'s `valid_irq_handlers`.** -/
theorem JAtZ.handlersJV (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : SInvV.ValidIrqHandlers σ) :
    HandlersActive (L.mem s) (L.ksb s) Z.G :=
  handlersActive_of_vih J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.2.1 J.xtop.fin.1.1.2.2.2.1 hV

set_option maxHeartbeats 4000000 in
/-- **The FL4 front keeps every slot** (`front_writes`: `FAULT_IP` and two node
words, none a slot word; as in g2c's `liveDN_front`). -/
theorem front_slotsSame (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR)
    (hA : P0.ArchTotal arI) {s' : S} {a' : A} (hF : KFrontB (L := L) arI s a s' a') :
    SlotsSame Z.th (L.mem s) (L.mem s') := by
  obtain ⟨ct, v, hct, hb⟩ := hF
  have hw := front_writes J hAK hA hct hb
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hta := J.ip.e.tcb ct hctT
  have h17 : layout.reg.FAULT_IP.val = 17 := by unfold layout.reg.FAULT_IP; rfl
  have hra : (regA ct layout.reg.FAULT_IP).val = ct.val + 392 := by
    rw [regA_val hta (by rw [h17]; omega), h17]
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hN : P1.NodePlaced st Z.T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hnv : ∀ o : U64, o.val < 4288 → (L.nodeAt s (L.cpu s) o).val = L.nodeBase s Z.c + o.val :=
    fun o ho => by rw [P1.nodeAt_val hN ho, hc.cur]
  have h48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
  have h40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have hCT := hnv _ (by rw [h48]; omega)
  have hCO := hnv _ (by rw [h40]; omega)
  rw [h48] at hCT; rw [h40] at hCO
  exact J.xtop.slotsSame_of hw fun b hb => by
    rcases hb with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨ct, hctT, by rw [hra]; omega, by rw [hra]; omega⟩))
    · exact Or.inl ⟨by rw [hCT]; omega, by rw [hCT]; omega⟩
    · exact Or.inl ⟨by rw [hCO]; omega, by rw [hCO]; omega⟩

set_option maxHeartbeats 4000000 in
/-- **`FlagsRel` from the entry state to the dispatch state** (as g2c's
`liveDN_front`): the FL4 front writes only `FAULT_IP` of the current thread
and two node words (`front_writes`), none a flags word `t+3456`; the spec's
FaultIP write replaces only the current TCB's registers. -/
theorem flags_front (hnd : Fl4Spec.numDomains = 1)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hFl : FlagsRel Z.T (L.mem s) σ)
    (hS : SInvAll.SInvB σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) {s' : S} {a' : A}
    (hF : KFrontB (L := L) arI s a s' a') {σb : Fl4Spec.State Unit} (hBA : BudgetAt σ σb true) :
    FlagsRel Z.T (L.mem s') σb := by
  obtain ⟨ct, v, hct, hb⟩ := hF
  have hw := front_writes J hAK hA hct hb
  obtain ⟨x, hk, -⟩ := hS.1.2
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hta := J.ip.e.tcb ct hctT
  have h17 : layout.reg.FAULT_IP.val = 17 := by unfold layout.reg.FAULT_IP; rfl
  have hra : (regA ct layout.reg.FAULT_IP).val = ct.val + 392 := by
    rw [regA_val hta (by rw [h17]; omega), h17]
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hN : P1.NodePlaced st Z.T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hnv : ∀ o : U64, o.val < 4288 → (L.nodeAt s (L.cpu s) o).val = L.nodeBase s Z.c + o.val :=
    fun o ho => by rw [P1.nodeAt_val hN ho, hc.cur]
  have hdj : ∀ t ∈ Z.T, t.val + 4096 ≤ L.nodeBase s Z.c ∨ L.nodeBase s Z.c + 4288 ≤ t.val := fun t ht => by
    have := hN.disj t ht; rw [hc.cur] at this; exact this
  have hal4 : ∀ t ∈ Z.T, t.val % 4096 = 0 := fun t ht => (J.ip.e.tcb t ht).align
  have h48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
  have h40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have hCT := hnv _ (by rw [h48]; omega)
  have hCO := hnv _ (by rw [h40]; omega)
  rw [h48] at hCT; rw [h40] at hCO
  have hct4 := hal4 ct hctT
  refine FlagsRel.frame hFl (fun t ht => ?_) (fun p y hy => ?_)
  · have htY := J.ip.e.tcb t ht
    have hv : (tFlagsWA t).val = t.val + 3456 := by
      unfold tFlagsWA; rw [P1.field_val htY (by decide)]; rfl
    have hy4 := hal4 t ht
    have hyd := hdj t ht
    refine hw.mem_eq (P1.field_aligned htY (by decide) (by decide)) ?_
    rintro (e | e | e)
    · have := congrArg UScalar.val e; rw [hv, hra] at this; omega
    · have := congrArg UScalar.val e; rw [hv, hCT] at this; omega
    · have := congrArg UScalar.val e; rw [hv, hCO] at this; omega
  · have ek : σb.kheap = Function.update σ.kheap σ.curThread
        (some (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))) :=
      (BudgetAt.shape27 hnd hk hBA).2.1
    rw [ek]
    by_cases hp : p = σ.curThread
    · subst hp
      rw [hk] at hy; cases hy
      exact ⟨_, Function.update_self .., rfl⟩
    · exact ⟨y, by rw [Function.update_of_ne hp]; exact hy, rfl⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- **The two spec-only entry facts left** (module docstring): l4v
`valid_ioports`, `untyped_ranges_zero`. -/
structure SInvIR (σ : Fl4Spec.State Unit) : Prop where
  ioP : SpecIoP σ
  utZ : SpecUtZ σ

theorem SInvIR.frame {σ σ' : Fl4Spec.State Unit} (h : SInvIR σ) (hcap : ∀ sl, SInvU.capAt σ' sl = SInvU.capAt σ sl)
    (ha : σ'.archState.x64AllocatedIoPorts = σ.archState.x64AllocatedIoPorts)
    (hm : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory) : SInvIR σ' where
  ioP sl f l hc := by rw [ha]; exact h.ioP sl f l (by rw [← hcap]; exact hc)
  utZ sl ptr sz fi hc a h1 h2 := by rw [hm]; exact h.utZ sl ptr sz fi (by rw [← hcap]; exact hc) a h1 h2

/-- **`SInvIR` from the entry state to the dispatch state** (as g5a's
`sinvI_disp`). -/
theorem sinvIR_disp (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hBA : BudgetAt σ σb true) (h : SInvIR σ) : SInvIR σb := by
  obtain ⟨⟨σu, hu, ebu⟩, ek, -⟩ := BudgetAt.shape27 hnd hk hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  refine h.frame (capAt_updTcb hk (by rfl) ek') ?_ ?_ <;> rw [ebu, e] <;> rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- `JEntryAtR5` to `JEntryAtR3` from `SInvX`'s `valid_irq_handlers` and `SInvIR`. -/
theorem _root_.Fl4Proofs.P3.JEntryAtR5.toR3V {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hV : SInvV.ValidIrqHandlers σ) (hI : SInvIR σ)
    (E : JEntryAtR5 (L := L) arI AR Z s ar σ) : JEntryAtR3 (L := L) arI AR Z s ar σ where
  stall := E.stall
  flags := E.flags
  handlers := J.handlersJV hV
  ports := J.portsJ hI.ioP
  ioapics := E.ioapics
  archIrq := E.archIrq
  vsTyp := E.vsTyp
  fnz := J.fnzJ
  urz := J.urzJ hI.utZ
  utks := J.utksJ

/-- `KDispHypsKV35E` to `KDispHypsKV35` from `valid_irq_handlers` and `SInvIR`. -/
theorem KDispHypsKV35E.to35V {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets}
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hV : SInvV.ValidIrqHandlers σ) (hI : SInvIR σ)
    (h : KDispHypsKV35E (L := L) arI AR MR Z H Cs D s a σ n c) :
    KDispHypsKV35 (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p, v⟩ := h.inv ct call bl don hct hi; ⟨e.toR3V J hV hI, p.to35 J, v⟩,
    fun ct rg sr cr hct hm => let ⟨e, p, v⟩ := h.mid ct rg sr cr hct hm; ⟨e.toR3V J hV hI, p.to35 J, v⟩⟩

/-- `valid_irq_handlers` at the dispatch state (the FaultIP write keeps every
cap, `update_time_stamp` the interrupt states). -/
theorem vih_disp (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hBA : BudgetAt σ σb true) (h : SInvV.ValidIrqHandlers σ) :
    SInvV.ValidIrqHandlers σb := by
  obtain ⟨⟨σu, hu, ebu⟩, ek, -⟩ := BudgetAt.shape27 hnd hk hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hi : σb.interruptStates = σ.interruptStates := by rw [ebu, e]; rfl
  intro p cref irq hc
  rw [hi]
  apply h p cref irq
  rw [ek'] at hc
  by_cases hp : p = σ.curThread
  · subst hp
    rw [Function.update_self] at hc
    rw [hk]; exact hc
  · rwa [Function.update_of_ne hp] at hc

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR5` without `flags`** (asked at the entry state and carried to
the dispatch state, `flags_front`): the three [P] fields and `vsTyp` [J]. -/
structure JEntryAtR6 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall` (one core). -/
  stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] joint `JEntryAt.vsTyp` (l4v `valid_cap` typ_at, `pspace_distinct`). -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)

/-- **`JPathME` without the frame path's `JFramePath`** (`hno`, from the
entry state's `LargeFrOK`): the Frame case asks only the VT-x scope part. -/
def JPathME6 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Frame p sz rt d m ep asid va =>
      ep = true ∨ lbl = fl4_abi.label.X86PageMapEPT → JVtxScope (L := L) arI AR s ar σ lbl length
        (.Frame p sz rt d m ep asid va) blk call don fp buf extra slbl argsU ci sl excaps buffer ct
  | c => JPathME (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c

/-- **`JPathAtM35E` with `JPathME6`.** -/
def JPathAtM36E (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (ct : U64) (is_call blocking can_donate first_phase : Bool) (cptr : U64) : Prop :=
  ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
    msg.msg_info st s ct = ok info →
    Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False) →
    msg.lookup_ipc_buffer st s false ct = ok buf →
    Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False) →
    ipc.lookup_extra_caps st s ct buf info = ok r2 →
    (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False) →
    Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False) →
    ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok c → Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) →
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c →
      JPathME6 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

variable {arI} in
theorem JPathAtM36E.to35E {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hM : MdbLinks Z.th (L.mem s) Z.G) (hLF : LargeFrOK Z.G (L.mem s))
    {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtM36E (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtM35E (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  cases c
  case Frame p sz rt d m ep asid va =>
    refine ⟨hP, fun hep => ⟨fun hsz hd x hx => ?_⟩⟩
    subst hep hsz hd
    obtain ⟨q, hq1, hq2⟩ := h8
    have hy : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨AbsSlot.isSlot ⟨q, hq1, Or.inl hq2⟩, _, h9, fun h => by cases h⟩
    exact hLF _ hy p rt m asid va (capV_of_capAt h9) x hx
  all_goals exact hP

/-- **`KDispHypsKV35E` with `JEntryAtR6` and `JPathAtM36E`.** -/
structure KDispHypsKV36E (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtM36E (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtM36E (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI}

theorem JEntryAtR6.toR5 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hFl : FlagsRel Z.T (L.mem s) σ) (E : JEntryAtR6 (L := L) arI AR Z s ar σ) :
    JEntryAtR5 (L := L) arI AR Z s ar σ :=
  ⟨E.stall, hFl, E.ioapics, E.archIrq, E.vsTyp⟩

theorem KDispHypsKV36E.to35E {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (hFl : FlagsRel Z.T (L.mem s) σ) (hM : MdbLinks Z.th (L.mem s) Z.G) (hLF : LargeFrOK Z.G (L.mem s))
    (h : KDispHypsKV36E (L := L) arI AR MR Z H Cs D s a σ n c) :
    KDispHypsKV35E (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p, v⟩ := h.inv ct call bl don hct hi; ⟨e.toR5 hFl, p.to35E hM hLF, v⟩,
    fun ct rg sr cr hct hm => let ⟨e, p, v⟩ := h.mid ct rg sr cr hct hm; ⟨e.toR5 hFl, p.to35E hM hLF, v⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ37` (post
`KPostXM`: an outcome related by `RJ`, with `MR` and `SInvX`) whose dispatch
bundle is `KDispHypsKV36E` (no `fnz` / `utks` / `handlers` / `ports` / `urz` /
`flags`, no Thread `hFr`, no Frame `hno`), given at the entry the spec-only
`hI : SInvIR σ` [J], the joint `hFl : FlagsRel Z.T (L.mem s) σ` [J] and the
FL4 `hLF : LargeFrOK Z.G (L.mem s)` [J].
Every other premise is `kernel_entryJ37`'s. -/
theorem kernel_entryJ36E [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ) (hI : SInvIR σ) (hFl : FlagsRel Z.T (L.mem s) σ)
    (hLF : LargeFrOK Z.G (L.mem s))
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV36E (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDM : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        JDispMRI (L := L) arI AR MR s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostXM (L := L) arI AR MR c σ r ⦄ := by
  obtain ⟨x, hk, -⟩ := hX.sb.1.2
  exact kernel_entryJ37 s a σ J hct hR hX n c hn hflag
    (fun σb hBA V' Ac' Lst' D' s' a' hF J' =>
      (KDispHypsKV36E.to35E (Z := Z.mv Z.G V')
        (flags_front hnd J hFl hX.sb hARI.toARKeep hA hF hBA) J'.xtop.rel.2.1.2.2.1
        (hLF.of_same (fun y hy => ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1)
          (front_slotsSame J hARI.toARKeep hA hF)) (hK σb hBA V' Ac' Lst' D' s' a' hF J')).to35V J' (vih_disp hnd hk hBA hX.sb.1.1.vih)
        (sinvIR_disp hnd hk hBA hI))
    hDM hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu hRef hPI hFast

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with `SInvIR`** (module docstring): `start`
from `JAtZ ∧ SInvX ∧ SInvIR ∧ MR`; `step` along `RJM` (what
`kernel_entryJ36E` delivers) with `SInvIR` of the exit (the open carry). -/
inductive JReachI : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SInvX σ → SInvIR σ → MR a σ.machineState → JReachI s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachI s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → SInvIR σ' → JReachI s' a' σ'

variable {arI AR MR}

/-- `JReachI` is `JReachM` (forget `SInvIR`). -/
theorem JReachI.toM {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachI (L := L) arI AR MR s a σ) :
    JReachM (L := L) arI AR MR s a σ := by
  induction h with
  | start J hX _ hR => exact JReachM.start J hX hR
  | step n c _ hct hn hv hy hRJ _ ih => exact JReachM.step n c ih hct hn hv hy hRJ

/-- **The invariant**: every `JReachI` state carries `JAtZ`, `SInvX`, `SInvIR`, `MR`. -/
theorem jreach_invI (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachI (L := L) arI AR MR s a σ) :
    (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) ∧ SInvX σ ∧ SInvIR σ ∧ MR a σ.machineState := by
  have hI : SInvIR σ := by
    cases h with
    | start _ _ hI _ => exact hI
    | step _ _ _ _ _ _ _ _ hI => exact hI
  obtain ⟨hJ, hX, hR⟩ := jreach_invM hnd h.toM
  exact ⟨hJ, hX, hI, hR⟩

set_option maxHeartbeats 4000000 in
/-- **Refinement at every `JReachI` state** (`kernel_entryJ36E`): at the
ghosts `jreach_invI` gives, the syscall entry from a non-idle thread refines
the spec's; every exit is related (`RJ`), satisfies `SInvX` and `MR`, and is
reachable again once `SInvIR` holds there (the open carry). Per-state
premises: `FlagsRel` and `LargeFrOK` at the entry, `hflag`, `hK` (now `KDispHypsKV36E`), `hDM` (`JDispMRI` [W]),
`hFin`, `hFast`. -/
theorem kernel_entry_reachI [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachI (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIR σ ∧ MR a σ.machineState ∧
      ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
      FlagsRel Z.T (L.mem s) σ → LargeFrOK Z.G (L.mem s) →
      (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
        ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          KDispHypsKV36E (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          JDispMRI (L := L) arI AR MR s' a' σb n c) →
      (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
        (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
          JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
          KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
      (n = fl4_abi.syscall.SysReplyRecv →
        FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) →
      syscall.handle_syscall st arI s a n ⦃ r => (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          (SInvIR σ' → JReachI (L := L) arI AR MR r.1 r.2 σ') ⦄ := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hI, hR⟩ := jreach_invI hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hI, hR, fun n c hct hn hFl hLF hflag hK hDM hFin hFast => ?_⟩
  have hE := kernel_entryJ36E (MR := MR) s a σ J hct hR hX hI hFl hLF n c hn hflag hK hDM hFin hARI hA hnd hM hKD hPA
    hIA hmrt hmb hT hmax htu hRef hPI hFast
  obtain ⟨⟨s', a'⟩, hv, hP⟩ := spec_exists hE
  rw [hv, WP.spec_ok]
  rcases hP with hF | ⟨σ', hy, hRJ, hM', hX'⟩
  · exact Or.inl hF
  · exact Or.inr ⟨σ', hy, hRJ, hX', hM', fun hI' => JReachI.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩ hI'⟩

end

end

end Fl4Proofs.P3.SInvR.G5
