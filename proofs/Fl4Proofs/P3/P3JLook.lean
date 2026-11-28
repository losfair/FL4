/-
P3 (line p3J, gen 2): **the path premises narrowed to the invoked slot** (inventory K1 / K4:
`JPathAtMU30`'s ∀-slot form is false on every SMP boot).

* **`LookAt ct cptr σ sl c`**: the spec's `lookupCapAndSlot ct (toBl cptr)` at `σ` has the single
  outcome `ok (absCap c, sl)` (l4v `lookup_cap_and_slot`, Syscall_A `handle_invocation`). With
  `capAt (L.mem s) (cslotAddr sl) = ok c` (already a hypothesis of every path premise) it pins the slot
  and the cap FL4's `cspace.lookup_slot` reads (`lookup_slot_refines`: the two lookups agree).
* `JPathAtM … JPathAtMU30` ↦ `JPathAtML … JPathAtMU29L`, **`JPathAtMU35`**: each the original with
  `LookAt ct cptr σ sl c →` after its last hypothesis (text copies, `scratch/p3J/genL.py`).
* The 16 conversions `JPathAtX.toY` re-proved on them (`…L`): the originals' proofs with the extra
  hypothesis passed through.
* **`handle_invocation_refinesMXPL`**: `handle_invocation_refinesMXP` with `hDec` asked only at the
  slot / cap the lookup returned (`LookAt`; the original proof has that outcome as `hl` where it applies
  `hDec`).
* `handle_invocation_entryJMUL`, `handle_invocation_entryJMUML`: the two consumers that apply the path
  premise (copies of `handle_invocation_entryJMU` / `Fl4ProofsQ.P3.handle_invocation_entryJMUM`).
No new premise; no sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU35
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3

/-- **The invoked slot**: the spec's `lookupCapAndSlot` for `cptr` at `σ` returns `(absCap c, sl)`
(l4v Syscall_A `handle_invocation`: `lookup_cap_and_slot thread cptr`). -/
def LookAt (ct cptr : Aeneas.Std.U64) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (c : fl4_core.capability.Cap) :
    Prop :=
  (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ = ({(.ok (absCap c, sl), σ)}, False)

end Fl4Proofs.P3

namespace Fl4Proofs.P3
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtM` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtML (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64) : Prop :=
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
      r2 = .Ok e → er = .ok exs → LookAt ct cptr σ sl c →
      JPathM (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3

namespace Fl4Proofs.P3
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtM35` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtM35L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathM (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3

namespace Fl4Proofs.P3
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}
variable (arI)

/-- **`JPathAtM35E` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtM35EL (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathME (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtM36E` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtM36EL (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathME6 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU4` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU4L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU4 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU7` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU7L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU7 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU12` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU12L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU12 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf
        e mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU17` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU17L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU17 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU18` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU18L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU18 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU19` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU19L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU19 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU21` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU21L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU21 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU25` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU25L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU25 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU26` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU26L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU26 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU27` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU27L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU27 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU28` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU28L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU28 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU29` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU29L (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU29 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathAtMU30` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, that `sl` / `c` are what the spec's `lookupCapAndSlot` returns for `cptr`. -/
def JPathAtMU35 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU30 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

/-- `JPathAtM35.toM` on the narrowed premises (P3JLook). -/
theorem JPathAtM35L.toML {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtM35L (L := L) arI AR Z H Cs D s a σ ct ic bl cd fp cptr) :
    JPathAtML (L := L) arI AR Z H Cs D s a σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs hsl hc hg hr he hL
  have hN : Vs.NativeCap c := by
    obtain ⟨p, h1', h2'⟩ := id hsl
    have hx : IsSlot Z.th (cslotAddr sl) := AbsSlot.isSlot ⟨p, h1', Or.inl h2'⟩
    have := J.ext.nat _ hx
    rwa [capV_of_capAt hc] at this
  exact h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs hsl hc hg hr he hN hL

end
end
end Fl4Proofs.P3

namespace Fl4Proofs.P3
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}
variable (arI)
variable {arI}

/-- `JPathAtM35E.to35` on the narrowed premises (P3JLook). -/
theorem JPathAtM35EL.to35L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtM35EL (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtM35L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr :=
  fun info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL =>
    (h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL).toM J

end
end
end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI} in

/-- `JPathAtM36E.to35E` on the narrowed premises (P3JLook). -/
theorem JPathAtM36EL.to35EL {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hM : MdbLinks Z.th (L.mem s) Z.G) (hLF : LargeFrOK Z.G (L.mem s))
    {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtM36EL (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtM35EL (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Frame p sz rt d m ep asid va =>
    refine ⟨hP, fun hep => ⟨fun hsz hd x hx hpx => ?_⟩⟩
    subst hep hsz hd
    obtain ⟨q, hq1, hq2⟩ := h8
    have hy : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨AbsSlot.isSlot ⟨q, hq1, Or.inl hq2⟩, _, h9, fun h => by cases h⟩
    exact hLF _ hy p rt m asid va (capV_of_capAt h9) x hx hpx
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

/-- `JPathAtMU4.to36E` on the narrowed premises (P3JLook). -/
theorem JPathAtMU4L.to36EL {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hT : TimeAgree arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtMU4L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtM36EL (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case SchedContext p sb =>
    exact ⟨fun hl => ⟨hT, hmb ar, hmax, htu ar, (hP hl).arch, (hP hl).rest⟩, fun _ => ⟨hmb ar, hmax, htu ar⟩⟩
  case SchedControl cpu =>
    exact ⟨hT, hmb ar, hmax, htu ar, hP.core, hP.arch, hP.rest⟩
  case AsidPool ptr base =>
    obtain ⟨-, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct h1 h2 h3 h4 h5 h6
    exact ⟨J.poolNative (hXO e exs h11 h12)⟩
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

/-- `JPathAtMU7.toU4` on the narrowed premises (P3JLook). -/
theorem JPathAtMU7L.toU4L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit} (hA : P0.ArchTotal arI)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtMU7L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU4L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  obtain ⟨-, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct h1 h2 h3 h4 h5 h6
  have hex := ExtraOK.rel1 J.xtop.rel.1 (hXO e exs h11 h12)
  obtain ⟨p0, hp1, hp2⟩ := h8
  have hAs : AbsSlot Z.th sl := ⟨p0, hp1, Or.inl hp2⟩
  have hslot : IsSlot Z.th (cslotAddr sl) := hAs.isSlot
  cases c <;> (try simp only [JPathMEU7] at hP)
  case SchedContext p sb =>
    exact fun hl => ⟨(hP hl).arch, fun H' Cs' Ac' Lst' D' J' =>
      WP.spec_mono (J'.scCtxStepP1 hA hni hct hslot h9 hl hex) fun _ hr _ _ _ => hr⟩
  case SchedControl cpu =>
    exact ⟨hP.core, hP.arch, fun H' Cs' Ac' Lst' D' J' =>
      WP.spec_mono (J'.scCtlStepP1 hA hni hct hP.core hex) fun _ hr _ _ _ _ _ _ _ => hr⟩
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU12.toU7` on the narrowed premises (P3JLook). -/
theorem JPathAtMU12L.toU7L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} (hG : DevGpm (L.mem s) Z.G σ)
    (h : JPathAtMU12L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU7L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev => exact ⟨fun hd => (hP.1 hd).toDev hG, hP.2⟩
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU17.toU12` on the narrowed premises (P3JLook). -/
theorem JPathAtMU17L.toU12L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} (hDF : DevFreeT (L.mem s) Z.G σ)
    (h : JPathAtMU17L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU12L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev => exact ⟨fun hd => JDevPathU17.toU12 (hP.1 hd) hDF, hP.2⟩
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU18.toU17` on the narrowed premises (P3JLook). -/
theorem JPathAtMU18L.toU17L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} (hC : JCarryS Z.B H σ)
    (h : JPathAtMU18L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU17L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev => exact ⟨fun hd => (hP.1 hd).toU17 hC, fun hd => (hP.2 hd).toM hC⟩
  case AsidControl => exact hP.toA hC
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU19.toU18` on the narrowed premises (P3JLook). -/
theorem JPathAtMU19L.toU18L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} (hC : JCarry (L := L) Z H Cs s σ)
    (h : JPathAtMU19L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU18L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev => exact ⟨fun hd => (hP.1 hd).toU18 hC, hP.2⟩
  case AsidControl => exact hP
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU21.toU19` on the narrowed premises (P3JLook). -/
theorem JPathAtMU21L.toU19L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hct : sched.cur_thread st s = ok ct)
    (h : JPathAtMU21L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU19L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev =>
    refine ⟨fun hd => ?_, hP.2⟩
    subst hd
    obtain ⟨pp, e1, hpp⟩ := h8
    have hAs : AbsSlot Z.th sl := ⟨pp, e1, Or.inl hpp⟩
    have hx : cslotAddr sl ∈ Z.G.chains.flatten :=
      (J.xtop.rel.2.1.2.2.1.members _).2 ⟨hAs.isSlot, _, h9, by simp⟩
    exact (hP.1 rfl).toU19 J hni hct hx (capV_of_capAt h9)
  case AsidControl => exact hP
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU25.toU21` on the narrowed premises (P3JLook). -/
theorem JPathAtMU25L.toU21L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (h : JPathAtMU25L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU21L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev =>
    exact ⟨fun hd => (hP.1 hd).toU21 J hni, fun hd => (hP.2 hd).toU16 J hni⟩
  case AsidControl => exact hP.toU16 J hni
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU26.toU25` on the narrowed premises (P3JLook). -/
theorem JPathAtMU26L.toU25L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (h : JPathAtMU26L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU25L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev =>
    exact ⟨fun hd => (hP.1 hd).toU25 J hni, fun hd => (hP.2 hd).toU25 J hni⟩
  case AsidControl => exact hP.toU25 J hni
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU27.toU26` on the narrowed premises (P3JLook). -/
theorem JPathAtMU27L.toU26L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (h : JPathAtMU27L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU26L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev =>
    exact ⟨fun hd => (hP.1 hd).toU26 J hni, fun hd => (hP.2 hd).toU26 J hni⟩
  case AsidControl => exact hP.toU26 J hni
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU28.toU27` on the narrowed premises (P3JLook). -/
theorem JPathAtMU28L.toU27L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (h : JPathAtMU28L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU27L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev =>
    exact ⟨fun hd => (hP.1 hd).toU27 J hni, fun hd => (hP.2 hd).toU27 J hni⟩
  case AsidControl => exact hP.toU27 J hni
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

set_option maxHeartbeats 4000000 in
/-- `JPathAtMU29.toU28` on the narrowed premises (P3JLook). -/
theorem JPathAtMU29L.toU28L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} [VxE Z]
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hct : sched.cur_thread st s = ok ct)
    (h : JPathAtMU29L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU28L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case Untyped p sb fi dev =>
    refine ⟨hP.1, fun hd => ?_⟩
    subst hd
    obtain ⟨pp, e1, hpp⟩ := h8
    have hAs : AbsSlot Z.th sl := ⟨pp, e1, Or.inl hpp⟩
    have hx : cslotAddr sl ∈ Z.G.chains.flatten :=
      (J.xtop.rel.2.1.2.2.1.members _).2 ⟨hAs.isSlot, _, h9, by simp⟩
    exact (hP.2 rfl).toU28 J hni hct hx (capV_of_capAt h9)
  case AsidControl => exact JAsidCPathU29.toU28 J hni hct
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3.SInvR.G5
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI}

/-- `JPathAtMU30.toU29` on the narrowed premises (P3JLook). -/
theorem JPathAtMU35.toU29L {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (hA : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (h : JPathAtMU35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU29L (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL
  cases c
  case SchedContext p sb =>
    exact fun _ => JSchedCtxPathU7.mk (decode_sched_context_keepAR P1.LawfulStore.total hA hK)
  case SchedControl cpu =>
    exact JSchedCPathU7.mk hP (decode_sched_control_keepAR P1.LawfulStore.total hA hK)
  all_goals exact hP

end
end
end Fl4Proofs.P3.SInvR.G5

namespace Fl4Proofs.P3
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`handle_invocation_refinesMXP` with `hDec` asked only at the slot the lookup returns** (`LookAt`, the lookup's own outcome `hl` in the original proof). -/
theorem handle_invocation_refinesMXPL (X XP : S → A → Fl4Spec.State Unit → Prop) (rep : Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (th : TypedHeap) (G : MdbGhost)
    (hP : Placed th) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hDR : DomRel (L.mem s) (L.ksb s) σ) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (hX0 : X s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    -- the front end's reads (`HIRead`)
    (info : msginfo.MessageInfo) (hinfo : msg.msg_info st s ct = ok info)
    (mi : Fl4Spec.MessageInfo) (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    (buf : U64) (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    (buffer : Option Fl4Spec.ObjRef)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr)))
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (hrr : (∃ e exs, r2 = .Ok e ∧ er = .ok exs) ∨
      (∃ f f', r2 = .Err f ∧ er = .error f' ∧ (blocking = true → faults.handle_fault st arI s ar ct f ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1, RelTopM (L := L) r.1 z.2 ∧ X r.1 r.2 z.2 ⦄)))
    (args : List Fl4Spec.Data) (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False))
    -- the fault of a failed lookup
    (hFL : blocking = true → ∀ lf lf', LookupFaultRel lf lf' →
      faults.handle_fault st arI s ar ct (.Cap cptr false lf) ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) false lf') σ).1,
          RelTopM (L := L) r.1 z.2 ∧ X r.1 r.2 z.2 ⦄)
    -- the success tail (from `X` with the invoker still current) and the error reply (at the entry state)
    (hRepS : ∀ (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit), RelTopM (L := L) s1 σ' → X s1 a1 σ' →
      σ'.curThread = ct.bv → flTail (st := st) ct is_call s1 a1 ⦃ res => res.1 = .Ok () ∧
        ∃ z ∈ (specTail is_call ct.bv [] σ').1, RelTopM (L := L) res.2.1 z.2 ∧ X res.2.1 res.2.2 z.2 ⦄)
    (hRepF : ∀ (a1 : A) (e : error.SysError) (e' : Fl4Spec.SyscallError), X s a1 σ → ErrRel (.Sys e) e' →
      ((if is_call then do
          let s2 ← syscall.reply_error st s ct e
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a1)) :
        Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
        res.1 = .Ok () ∧ ∃ z ∈ ((Fl4Spec.NonDet.when is_call <|
          Fl4Spec.fl4ReplyFromKernelError rep ct.bv (Fl4Spec.msgFromSyscallError e')) σ).1,
          RelTopM (L := L) res.2.1 z.2 ∧ X res.2.1 res.2.2 z.2 ⦄)
    -- the invocation keeps the current thread
    (hPK : ∀ inv σ1 y, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blocking is_call can_donate inv).run σ1).1 →
      y.2.curThread = ct.bv)
    -- the decode and invocation of the cap
    (hDec : ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok c →
      Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →
      LookAt ct cptr σ sl c → XCapP (L := L) arI X XP s ar σ info.label (msgLen info buf) (cslotAddr sl) c blocking is_call can_donate
        first_phase buf e mi.miLabel args (Fl4Spec.toBl cptr.bv) sl exs buffer ct) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) X XP rep σ is_call blocking can_donate first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  have hRT0 : RelTopM (L := L) s σ := ⟨th, G, hP, hCR, hFI, hDR, hFR⟩
  unfold syscall.handle_invocation
  rw [hct]; simp only [bind_ok, hinfo]
  refine WP.spec_bind (lookup_slot_refines (Z := Unit) th s σ hCR.1 hCR.2.1 ct htcb cptr) ?_
  rintro r ⟨e, he, hrel, hok⟩
  cases r with
  | Err lf =>
    cases e with
    | ok v => exact hrel.elim
    | error lf' =>
      simp only
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.error lf', σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot; exact run_bind_error (s := σ) he _
      have hmF := hiMF_lookup_err (mi := mi) hl
      cases blocking
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨(.ok (), σ), hi_memR rep hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
          (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0, ifP_ok rfl hX0⟩
      · simp only [↓reduceIte]
        refine WP.spec_bind (hFL rfl lf lf' hrel) ?_
        rintro ⟨s1, a1⟩ ⟨z, hz, hRT, hXz⟩
        refine (WP.spec_ok _).2 ?_
        exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
          Or.inl ⟨rfl, rfl⟩, hRT, ifP_ok rfl hXz⟩
  | Ok r1 =>
    cases e with
    | error lf' => exact hrel.elim
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth, -⟩ := hok
      obtain ⟨c, a, hc, hca, hget⟩ := hCR.1.slot_cap hp hth
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.ok (a, sl), σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot
        rw [run_bind_ok he]
        simp only
        rw [run_bind_ok (run_liftE hget)]
        rfl
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, hbuf, hr2]
      rcases hrr with ⟨ex, exs, rfl, rfl⟩ | ⟨f, f', rfl, rfl, hfh⟩
      · simp only
        rw [msgLen_eq]; simp only [bind_ok]
        have hca' : absCap c = a := hca.2
        subst hca'
        have hmF := hiMF_ok (mi := mi) hl hbuffer her
        have hmE := hiME_run (cptr := Fl4Spec.toBl cptr.bv) (fp := first_phase) (a := absCap c) (sl := sl)
          (exs := exs) hmrs
        rcases hDec sl c ex exs ⟨p, hp, hth⟩ hc hget rfl rfl hl with hD | hD
        swap
        · refine WP.spec_bind hD ?_
          rintro ⟨r3, s1, a1⟩ (⟨e3, he3, hs1, ⟨e', hdec, herr⟩, hXe⟩ | ⟨hok3, hne, inv, hdec, σ1, hst, rr, σy, hy, z, hz, hRT, hXz⟩)
          · simp only at he3 hs1
            subst he3 hs1
            cases e3 with
            | Sys e2 =>
              refine WP.spec_mono (hRepF a1 e2 e' hXe herr) ?_
              rintro res ⟨hres, z, hz, hRT, hXz⟩
              exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
                Or.inl ⟨hres, rfl⟩, hRT, ifP_ok hres hXz⟩
            | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          simp only at hok3; subst hok3
          refine WP.spec_bind (tcb_state_spec' (st := st) s1 ct) ?_
          rintro v rfl
          rw [if_neg hne]
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
            (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨rfl, rfl⟩, hRT, ifP_ok rfl hXz⟩
        refine WP.spec_bind hD ?_
        rintro ⟨r3, s1, a1⟩ hq
        rcases hq with ⟨e3, he3, hs1, ⟨e', hdec, herr⟩, hXe⟩ |
            ⟨inv, hdec, σ1, hst, y, hy, ⟨th', G', hcase, hP', hCR', hFI', hDR', hFR'⟩, hXy⟩
        · simp only at he3 hs1
          subst he3 hs1
          cases e3 with
          | Sys e2 =>
            refine WP.spec_mono (hRepF a1 e2 e' (ifP_X (r := .Err (.Sys e2)) (fun h => by cases h) hXe) herr) ?_
            rintro res ⟨hres, z, hz, hRT, hXz⟩
            exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
              Or.inl ⟨hres, rfl⟩, hRT, ifP_ok hres hXz⟩
          | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
        · rcases hcase with ⟨hok3, hyr⟩ | ⟨hpre, hyr⟩
          · simp only at hok3
            subst hok3
            refine WP.spec_mono (hRepS s1 a1 y.2 ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩ (ifP_X (r := .Ok ()) (fun h => by cases h) hXy)
              (hPK inv σ1 y hst hy)) ?_
            rintro res ⟨hres, z, hz, hRT, hXz⟩
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨hres, rfl⟩, hRT, ifP_ok hres hXz⟩
          · simp only at hpre
            subst hpre
            refine (WP.spec_ok _).2 ?_
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.error (), y2), hi_memR rep hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_pre (by rw [← hcur]; exact hst) hy)), Or.inr ⟨rfl, rfl⟩,
              ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩, hXy⟩
      · simp only
        have hmF := hiMF_extra_err (cptr := Fl4Spec.toBl cptr.bv) hl hbuffer her
        cases blocking
        · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨(.ok (), σ), hi_memR rep hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
            (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0, ifP_ok rfl hX0⟩
        · simp only [↓reduceIte]
          refine WP.spec_bind (hfh rfl) ?_
          rintro ⟨s1, a1⟩ ⟨z, hz, hRT, hXz⟩
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_memR rep hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
            Or.inl ⟨rfl, rfl⟩, hRT, ifP_ok rfl hXz⟩

end
end
end Fl4Proofs.P3

namespace Fl4Proofs.P3
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- `handle_invocation_entryJMU` on `JPathAtML` (P3JLook). -/
theorem handle_invocation_entryJMUL [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtML (L := L) arI AR Z H Cs D s ar σ ct is_call blocking can_donate first_phase cptr)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hNs : NativeScope σ) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) true σ is_call blocking can_donate
        first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hX := J.xtop
  refine handle_invocation_refinesMXPL arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) true s ar σ Z.th Z.G
    hX.rel.1 hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 hX.rel.2.2.2.2.1 ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩ ct hct hcur htcb
    is_call blocking can_donate first_phase cptr info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her
    ((J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf
      hbuffer hr2 her).imp id fun ⟨f, f', h1, h2, hcf⟩ => ⟨f, f', h1, h2, fun _ =>
      J.faultHypJZ hG.tot hE.ni hct hE.ctnq hE.vfh hcf⟩)
    (argsU.map UScalar.bv) hmrs
    (fun _ lf lf' hl => J.faultHypJZ hG.tot hE.ni hct hE.ctnq hE.vfh
      (capFaultCorr_lookup cptr hl))
    (fun s1 a1 σ' _ ⟨_, _, _, _, _, _, J', _⟩ hc => J'.flTailJ hc is_call)
    (fun a1 e e' ⟨_, _, _, _, _, _, J'', _⟩ he =>
      (J.archJ J''.xtop.fin.1.1.2.2.2.2.2.2).replyFailJ hcur
        is_call e e' he)
    (fun inv σ1 y hst hy => by
      rw [perfCurKeep _ _ _ inv σ1 y hy]
      obtain ⟨x, hk⟩ := (J.xtop.curTcb hcur).2
      rw [hcur] at hst
      have hm : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
        rw [hst]; exact Set.mem_singleton _
      rw [Notif.setThreadState_eq .restart hk] at hm
      have e : σ1 = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      rw [e, Sched.stsAct_rec]; exact hcur) ?_
  obtain ⟨hLen, hArgs, hA5⟩ := J.argsJ J.xferH.1 J.xferH.2.1
    hct hinfo hmi hbuf hbuffer hmrs
  intro sl c e exs hsl hc hget h1 h2 hL
  have hl : argsU.length ≤ 120 := by
    have hm := Endp.msg_info_spec (L := L) s ct
    rw [hinfo, WP.spec_ok] at hm
    have h120 := hm.2.2.2
    have h4 : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
    rw [← hLen]; unfold msgLen
    split_ifs <;> omega
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct
    hinfo hmi hbuf hbuffer hr2 her
  have hXN : ExtraNamed Z.th (L.mem s) e := by
    have h := lookup_extra_named Z.th s σ J.dstate.1.1 J.dstate.1.2.1 htcb buf info
    rw [hr2, WP.spec_ok] at h
    exact h e h1
  exact decOK_JMU arI s ar σ J hG hE ct hct info.label (msgLen info buf) blocking is_call can_donate first_phase
    buf e mi.miLabel argsU hLen hArgs hbuf hl (Fl4Spec.toBl cptr.bv) sl hsl c hc exs buffer
    (hXO e exs h1 h2) hXN hLb hA5 (hP info mi buf buffer r2 er argsU hinfo hmi hbuf hbuffer hr2 her hmrs sl c e exs hsl hc hget h1 h2 hL)
    hPD hR hVT hVI hNs

end
end
end Fl4Proofs.P3

namespace Fl4Proofs.P3
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- `Fl4ProofsQ.P3.handle_invocation_entryJMUM` on `JPathAtML` (P3JLook). -/
theorem handle_invocation_entryJMUML [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtML (L := L) arI AR Z H Cs D s ar σ ct is_call blocking can_donate first_phase cptr)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct)
    (hDL : JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hNs : NativeScope σ) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) true σ is_call blocking can_donate
        first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  have hA := hG.tot
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hX := J.xtop
  have hF : ∀ {f : error.Fault} {f' : Fl4Spec.Fault}, CapFaultCorr f f' →
      faults.handle_fault st arI s ar ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
        RelTopM (L := L) r.1 z.2 ∧ JAtM (L := L) arI AR MR r.1 r.2 z.2 ⦄ := fun hcf =>
    WP.spec_mono (Fl4Proofs.P3.spec_mrz hM (J.faultHypJZ hA hE.ni hct hE.ctnq hE.vfh hcf)
      (MKD.faults_handle_fault L.total hA hKD hR)
      (fun z hz => congrArg Prod.fst (MachT.mtk_handleFaultG _ _ σ z hz)))
      fun _ ⟨z, hz, ⟨h1, h2⟩, h3⟩ => ⟨z, hz, h1, h2, h3⟩
  refine handle_invocation_refinesMXPL arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) true s ar σ Z.th Z.G
    hX.rel.1 hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 hX.rel.2.2.2.2.1 ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hR⟩ ct hct hcur htcb
    is_call blocking can_donate first_phase cptr info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her
    ((J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf
      hbuffer hr2 her).imp id fun ⟨f, f', h1, h2, hcf⟩ => ⟨f, f', h1, h2, fun _ => hF hcf⟩)
    (argsU.map UScalar.bv) hmrs
    (fun _ lf lf' hl => hF (capFaultCorr_lookup cptr hl))
    (fun s1 a1 σ' _ ⟨⟨_, _, _, _, _, _, J', _⟩, hR'⟩ hc =>
      WP.spec_mono (WP.spec_and (J'.flTailJ hc is_call) (MKD.fl_tail L.total hA hKD hR'))
        fun _ ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ => ⟨h1, z, hz, h2, h3, Fl4Proofs.P3.msF_mr hM h4
          (congrArg Prod.fst (MachT.mtk_specTailG _ _ _ σ' z hz))⟩)
    (fun a1 e e' ⟨⟨_, _, _, _, _, _, J'', _⟩, hR'⟩ he =>
      WP.spec_mono (WP.spec_and ((J.archJ J''.xtop.fin.1.1.2.2.2.2.2.2).replyFailJ hcur is_call e e' he)
        (MKD.reply_err_tail (e := e) (t := ct) (s := s) (is_call := is_call) L.total hA hKD hR'))
        fun _ ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ => ⟨h1, z, hz, h2, h3, Fl4Proofs.P3.msF_mr hM h4
          (congrArg Prod.fst (MachT.mtk_when (MachT.mtk_fl4ReplyFromKernelErrorG _ _ _) σ z hz))⟩)
    (fun inv σ1 y hst hy => by
      rw [perfCurKeep _ _ _ inv σ1 y hy]
      obtain ⟨x, hk⟩ := (J.xtop.curTcb hcur).2
      rw [hcur] at hst
      have hm : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
        rw [hst]; exact Set.mem_singleton _
      rw [Notif.setThreadState_eq .restart hk] at hm
      have e : σ1 = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      rw [e, Sched.stsAct_rec]; exact hcur) ?_
  obtain ⟨hLen, hArgs, hA5⟩ := J.argsJ J.xferH.1 J.xferH.2.1
    hct hinfo hmi hbuf hbuffer hmrs
  intro sl c e exs hsl hc hget h1 h2 hL
  have hl : argsU.length ≤ 120 := by
    have hm := Endp.msg_info_spec (L := L) s ct
    rw [hinfo, WP.spec_ok] at hm
    have h120 := hm.2.2.2
    have h4 : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
    rw [← hLen]; unfold msgLen
    split_ifs <;> omega
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct
    hinfo hmi hbuf hbuffer hr2 her
  have hXN : ExtraNamed Z.th (L.mem s) e := by
    have h := lookup_extra_named Z.th s σ J.dstate.1.1 J.dstate.1.2.1 htcb buf info
    rw [hr2, WP.spec_ok] at h
    exact h e h1
  exact Fl4Proofs.P3.decOK_JMM arI s ar σ J hG hE ct hct info.label (msgLen info buf) blocking is_call can_donate first_phase
    buf e mi.miLabel argsU hLen hArgs hbuf hl (Fl4Spec.toBl cptr.bv) sl hsl c hc exs buffer
    (hXO e exs h1 h2) hXN hLb hA5 (hP info mi buf buffer r2 er argsU hinfo hmi hbuf hbuffer hr2 her hmrs sl c e exs hsl hc hget h1 h2 hL)
    hPD hDL hR hVT hVI hNs hM hKD hA

end
end
end Fl4Proofs.P3
