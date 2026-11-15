/-
P3 (DESIGN.md §9), endpoints: the spec's message transfer, computed.

On a state where the sender and receiver are distinct TCBs, the sender has
no fault and the receiver has no IPC buffer (`ipcBufOf true = none`), l4v
`do_ipc_transfer` with no extra caps (`grant = false`, or the message
names none, or the sender has no IPC buffer) has exactly one outcome
(`doIpcTransfer_regs`): the receiver gets the first `min len 4` message
registers of the sender (`copyRegsTcb`), the message info
`⦇min len 4, 0, 0, label⦈` and the badge.
-/
import Fl4Proofs.P3.EpRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

variable {Z : Type}

/-- The spec's IPC buffer of a TCB (l4v X64 `lookup_ipc_buffer`, as a
function of the TCB). -/
def ipcBufOf (isRecv : Bool) (x : Tcb) : Option ObjRef :=
  match x.tcbIpcframe with
  | .archObjectCap (.pageCap _ p R _ vms _) =>
      if vmReadWrite ⊆ R ∨ vmReadOnly ⊆ R ∧ ¬isRecv
      then some (p + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms)))
      else none
  | _ => none

theorem updK_self {σ : State Z} {p : ObjRef} {o : KernelObject} (hk : σ.kheap p = some o) : updK σ p o = σ := by
  unfold updK
  rw [← hk, Function.update_eq_self]

theorem tcbCnodeMap_two (x : Tcb) : tcbCnodeMap x (tcbCnodeIndex 2) = some x.tcbIpcframe := by
  unfold tcbCnodeMap
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self]

theorem getCap_tcb_two {σ : State Z} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    getCap (Z := Z) (t, tcbCnodeIndex 2) σ = ({(x.tcbIpcframe, σ)}, False) := by
  unfold getCap
  dsimp only
  rw [nd_bind_one (getObject_eq hk)]
  dsimp only
  rw [nd_pure_bind', tcbCnodeMap_two]
  rfl

theorem lookupIpcBuffer_eq {σ : State Z} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (b : Bool) :
    lookupIpcBuffer (Z := Z) b t σ = ({(ipcBufOf b x, σ)}, False) := by
  unfold lookupIpcBuffer
  rw [nd_bind_one (threadGet_eq _ hk), nd_pure_bind', nd_bind_one (getCap_tcb_two hk)]
  unfold ipcBufOf
  generalize x.tcbIpcframe = c
  cases c with
  | archObjectCap a =>
    cases a with
    | pageCap d p R mt vms m => dsimp only; split <;> rfl
    | _ => rfl
  | _ => rfl

theorem asUser_getRegister_eq {σ : State Z} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (r : Register) :
    asUser (Z := Z) t (getRegister r) σ = ({(x.tcbArch.tcbContext.userRegs r, σ)}, False) := by
  unfold asUser
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  show ((pure _ : NonDet (State Z) UserContext) >>= _) σ = _
  rw [nd_pure_bind']
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.selectF (σ := State Z) (getRegister r (archTcbContextGet x.tcbArch)) σ =
      (({((x.tcbArch.tcbContext.userRegs r, archTcbContextGet x.tcbArch), σ)}), False) by
    simp only [NonDet.selectF, getRegister, NonDet.gets]
    ext ⟨a, b⟩ <;> simp [archTcbContextGet])]
  show ((pure _ : NonDet (State Z) Tcb) >>= _) σ = _
  rw [nd_pure_bind']
  have hx : ({ x with tcbArch := archTcbContextSet (archTcbContextGet x.tcbArch) x.tcbArch } : Tcb) = x := rfl
  rw [hx]
  refine (nd_bind_one (setObject_eq (o' := KernelObject.tcb x) hk rfl) _).trans ?_
  rw [updK_self hk]; rfl

theorem getMessageInfo_eq {σ : State Z} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    getMessageInfo (Z := Z) t σ =
      ({(dataToMessageInfo (x.tcbArch.tcbContext.userRegs msg_info_register), σ)}, False) := by
  unfold getMessageInfo
  rw [nd_bind_one (asUser_getRegister_eq hk _)]; rfl

/-- The receiver `x` with the registers `rs` taken from `vals`. -/
def copyRegsTcb (x : Tcb) (vals : Register → Word) (rs : List Register) : Tcb :=
  rs.foldl (fun acc r => setReg acc r (vals r)) x

theorem copyRegsTcb_regs (x : Tcb) (vals : Register → Word) :
    ∀ rs : List Register, ∀ r, (copyRegsTcb x vals rs).tcbArch.tcbContext.userRegs r =
      if r ∈ rs then vals r else x.tcbArch.tcbContext.userRegs r
  | [], r => by simp [copyRegsTcb]
  | r' :: rs, r => by
    show (copyRegsTcb (setReg x r' (vals r')) vals rs).tcbArch.tcbContext.userRegs r = _
    rw [copyRegsTcb_regs _ vals rs r]
    by_cases h : r ∈ rs
    · simp [h]
    · by_cases e : r = r'
      · subst e; simp [h, setReg, setRegUc, archTcbContextSet, archTcbContextGet]
      · simp [h, e, setReg, setRegUc, archTcbContextSet, archTcbContextGet, Function.update_of_ne e]

theorem copyRegsTcb_other (x : Tcb) (vals : Register → Word) :
    ∀ rs : List Register, copyRegsTcb x vals rs = { x with tcbArch := (copyRegsTcb x vals rs).tcbArch }
  | [] => rfl
  | r' :: rs => by
    show copyRegsTcb (setReg x r' (vals r')) vals rs = _
    rw [copyRegsTcb_other _ vals rs]
    rfl

/-- Copying the registers `rs` from the sender to the receiver. -/
theorem copy_regs_eq {σ : State Z} {snd rcv : ObjRef} {xs xr : Tcb} (hne : snd ≠ rcv)
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) :
    ∀ rs : List Register,
      NonDet.mapM (fun r => do
          let v ← asUser (Z := Z) snd <| getRegister r
          asUser rcv <| setRegister r v) rs σ =
        ({(rs.map fun _ => (), updK σ rcv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs rs)))}, False)
  | [] => by
    show (pure [] : NonDet (State Z) (List Unit)) σ = ({([], updK σ rcv (.tcb xr))}, False)
    rw [nd_pure_apply', updK_self hkr]
  | r :: rs => by
    unfold NonDet.mapM
    rw [nd_bind_one' (show (do
          let v ← asUser (Z := Z) snd <| getRegister r
          asUser rcv <| setRegister r v) σ = ({((), updK σ rcv (.tcb (setReg xr r (xs.tcbArch.tcbContext.userRegs r))))},
          False) by
        rw [nd_bind_one (asUser_getRegister_eq hks r), asUser_setRegister_eq _ _ hkr])]
    have hks' : (updK σ rcv (.tcb (setReg xr r (xs.tcbArch.tcbContext.userRegs r)))).kheap snd = some (.tcb xs) := by
      simp [hne, hks]
    have hkr' : (updK σ rcv (.tcb (setReg xr r (xs.tcbArch.tcbContext.userRegs r)))).kheap rcv =
        some (.tcb (setReg xr r (xs.tcbArch.tcbContext.userRegs r))) := by simp
    rw [nd_bind_one' (copy_regs_eq hne hks' hkr' rs)]
    show ({_}, False) = _
    simp only [updK, Function.update_idem]
    rfl

theorem getExtraCptrs_nil {σ : State Z} {sbuf : Option ObjRef} {mi : MessageInfo}
    (h : sbuf = none ∨ unat mi.miExtraCaps = 0) : getExtraCptrs (Z := Z) sbuf mi σ = ({([], σ)}, False) := by
  rcases h with rfl | h
  · rfl
  · cases sbuf with
    | none => rfl
    | some b =>
      unfold getExtraCptrs
      dsimp only
      rw [h, Nat.add_zero, Nat.sub_self]
      unfold NonDet.liftM
      exact nd_bind_one' (show NonDet.mapM (loadWordOffs (Z := Z) b) [] σ = ({([], σ)}, False) from rfl) _

theorem runE_liftE_bind {ε α β : Type} {m : NonDet (State Z) α} {f : α → NonDetE (State Z) ε β} {s : State Z} {a : α}
    (h : m s = ({(a, s)}, False)) : ExceptT.run (NonDetE.liftE m >>= f) s = ExceptT.run (f a) s := by
  show NonDet.bind (NonDet.bind m (fun a => NonDet.pure (Except.ok a))) (ExceptT.bindCont f) s = _
  rw [nd_bind_one' (show NonDet.bind m (fun a => NonDet.pure (Except.ok a)) s = ({(Except.ok a, s)}, False) by
    rw [nd_bind_one' h]; rfl)]
  rfl

theorem catch_lookupExtraCaps_nil {σ : State Z} {snd : ObjRef} {sbuf : Option ObjRef} {mi : MessageInfo}
    (h : sbuf = none ∨ unat mi.miExtraCaps = 0) :
    NonDetE.catch (lookupExtraCaps (Z := Z) snd sbuf mi) (fun _ => pure []) σ = ({([], σ)}, False) := by
  have hg := getExtraCptrs_nil (Z := Z) (σ := σ) h
  unfold NonDetE.catch lookupExtraCaps
  rw [nd_bind_one' (show ExceptT.run (NonDetE.liftE (getExtraCptrs sbuf mi) >>= fun cptrs =>
      NonDetE.mapME (fun cptr => capFaultOnFailure (ofBl cptr) false (lookupCapAndSlot snd cptr)) cptrs) σ =
      ({(Except.ok [], σ)}, False) by rw [runE_liftE_bind hg]; rfl)]
  rfl

/-- The message info the receiver gets, from the sender's message info
register `w`, when no buffer words are copied. -/
def xferInfo (w : Word) : MessageInfo :=
  let mi := dataToMessageInfo w
  ⟨min mi.miLength (natToLen ((msg_registers.take (unat mi.miLength)).length + ([] : List Word).length)), 0, 0,
    mi.miLabel⟩

/-- The receiver after a register-only transfer. -/
def xferTcb (xr xs : Tcb) (badge : Badge) : Tcb :=
  let w := xs.tcbArch.tcbContext.userRegs msg_info_register
  setReg (setReg (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
      (msg_registers.take (unat (dataToMessageInfo w).miLength)))
    msg_info_register (messageInfoToData (xferInfo w))) badge_register badge

theorem copyMrs_noRecvBuf {σ : State Z} {snd rcv : ObjRef} {xs xr : Tcb} (hne : snd ≠ rcv)
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) (sbuf : Option ObjRef)
    (n : LengthType) :
    copyMrs (Z := Z) snd sbuf rcv none n σ =
      ({(min n (natToLen ((msg_registers.take (unat n)).length + ([] : List Word).length)),
        updK σ rcv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (msg_registers.take (unat n)))))}, False) := by
  unfold copyMrs
  rw [nd_pure_bind', nd_bind_one (copy_regs_eq hne hks hkr _)]
  cases sbuf <;> (dsimp only; rw [nd_pure_bind']; rfl)

theorem transferCaps_noRecvBuf {σ : State Unit} (mi : MessageInfo) (ep : Option ObjRef) (rcv : ObjRef) :
    transferCaps (Z := Unit) mi [] ep rcv none σ = ({(⟨mi.miLength, 0, 0, mi.miLabel⟩, σ)}, False) := by
  unfold transferCaps
  rw [nd_bind_one (show getReceiveSlots (Z := Unit) rcv none σ = ({([], σ)}, False) from rfl), nd_pure_bind']
  rfl

/-- **`do_ipc_transfer`, registers only**: the receiver has no IPC buffer,
the sender no fault, and there are no extra caps to look up. -/
theorem doIpcTransfer_regs {σ : State Unit} {snd rcv : ObjRef} {xs xr : Tcb} (hne : snd ≠ rcv)
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : ipcBufOf true xr = none) (ep : Option ObjRef) (badge : Badge) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      unat (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miExtraCaps = 0) :
    doIpcTransfer (Z := Unit) snd ep badge grant rcv σ = ({((), updK σ rcv (.tcb (xferTcb xr xs badge)))}, False) := by
  unfold doIpcTransfer
  rw [nd_bind_one (lookupIpcBuffer_eq hkr true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hks false)]
  unfold doNormalTransfer
  rw [nd_bind_one (getMessageInfo_eq hks)]
  have hlk : grant = true → NonDetE.catch (lookupExtraCaps (Z := Unit) snd (ipcBufOf false xs)
      (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register))) (fun _ => pure []) σ =
      ({([], σ)}, False) := by
    intro hg
    refine catch_lookupExtraCaps_nil ?_
    rcases hcaps with h | h | h
    · rw [hg] at h; cases h
    · exact Or.inl h
    · exact Or.inr h
  cases grant <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    first | rw [nd_bind_one (hlk rfl)] | rw [nd_pure_bind']
  all_goals
    rw [nd_bind_one (copyMrs_noRecvBuf hne hks hkr _ _), nd_bind_one (transferCaps_noRecvBuf _ _ _)]
    have hkr1 : (updK σ rcv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (msg_registers.take (unat (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLength))))).kheap
        rcv = some (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (msg_registers.take (unat (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLength)))) := by
      simp
    unfold setMessageInfo
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkr1)]
    rw [asUser_setRegister_eq (x := setReg (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (msg_registers.take (unat (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLength)))
        msg_info_register (messageInfoToData (xferInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)))) _ _
        (by simp only [updK_kheap, Function.update_self]; rfl)]
    simp only [updK, Function.update_idem]
    rfl

end

end Fl4Proofs.P3.Endp
