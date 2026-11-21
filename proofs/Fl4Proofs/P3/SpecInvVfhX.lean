/-
P3 (DESIGN.md §9), invariant line G1 (vfh3): **the decode's carry for VfhAll,
arch and untyped decodes, and the dispatcher** (spec side only, outside the
JAtZ cone; vfh2 handoff steps 1 and 3, decode half).

* `DRef σ0 p`: some slot of `σ0` holds a CNode cap to `p` (the object a lookup
  lands in is named by a slot cap: what the retype performs need to keep the
  destination CNode out of a reset region, SpecInvVfhR). `RootSl σ0 c`: a CNode
  cap `c` names such an object (it sits in a slot). `vfh_rabR`,
  `vfh_lookupTargetSlotR` (the target slot is not a fault-handler slot and its
  CNode is `DRef`), `vfh_okv_nodeCap` (the untyped / DeriveSubframe node cap).
* `vfh_natToCref_notBad`: slot `natToCref r k` of a full CNode of radix `r` is
  no fault-handler slot (its length is `min r 64`, so it is `tcbCnodeIndex 3`
  only for `r = 3`, and then index 6 is held).
* `VArch σ0` (map / unmap: the invoked slot `cte`, not `Bad` by `VfhV` since it
  holds an arch cap, and an arch cap; IO port control: the target slot;
  MakePool `VMp`: the target slot and its `DRef`; DeriveSubframe: every
  destination) and `vfh_okv_fl4ArchDecode`; `VUt σ0` (every retype destination
  not `Bad` and `DRef`) and `vfh_okv_decodeUntyped`.
* `VInv σ0` (CNode `VCn`, IRQ control `VFl4IrqC`, IRQ handler `VIh`, TCB
  `VTcb`, arch `VArch`, untyped `VUt`) and **`vfh_okv_fl4Decode`**.
-/
import Fl4Proofs.P3.SpecInvVfhA
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Slot references -/

/-- Some slot of `σ0` holds a CNode cap to `p`. -/
def DRef (σ0 : State Unit) (p : ObjRef) : Prop :=
  ∃ (s : CslotPtr) (r : Nat) (g : CapRef), capOpt (σ0.kheap s.1) s.2 = some (.cnodeCap p r g)

/-- A CNode cap `c` names an object some slot's CNode cap names. -/
def RootSl (σ0 : State Unit) (c : Cap) : Prop := ∀ p r g, c = .cnodeCap p r g → DRef σ0 p

theorem vfh_rootSl_of {σ0 : State Unit} {s : CslotPtr} {c : Cap} (h : capOpt (σ0.kheap s.1) s.2 = some c) :
    RootSl σ0 c := fun p r g e => ⟨s, r, g, e ▸ h⟩

/-- `resolve_address_bits'` from a root sitting in a slot lands in a `DRef` object. -/
theorem vfh_rabR (σ0 : State Unit) (p : Cap × CapRef) (hc : RootSl σ0 p.1) :
    OkV σ0 (fun r : CslotPtr × CapRef => DRef σ0 r.1.1) (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · rename_i oref radix guard heq
    have hr : DRef σ0 oref := hc oref radix guard heq
    split
    · exact vfh_okv_liftE_fail
    · refine vfh_okv_whenE_bind _ _ fun _ => vfh_okv_whenE_bind _ _ fun _ => ?_
      refine okv_returnOk_bind ?_
      dsimp only
      split
      · exact okv_returnOk hr
      · refine okv_bind (vfh_okv_getCap _) fun nc hnc => ?_
        split
        · exact vfh_rabR σ0 _ (vfh_rootSl_of hnc)
        · exact okv_returnOk hr
  · exact okv_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega

theorem vfh_lookupSlotForCnodeOpR (σ0 : State Unit) (isSource : Bool) (croot : Cap) (ptr : CapRef)
    (depth : Nat) (hc : RootSl σ0 croot) :
    OkV σ0 (fun sl : CslotPtr => DRef σ0 sl.1) (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp
  split
  · refine vfh_okv_whenE_bind _ _ fun _ => ?_
    unfold lookupErrorOnFailure
    refine vfh_okv_handleE ?_ (fun e s0 => okdAt_throw _)
    refine okv_returnOk_bind ?_
    unfold resolveAddressBits
    refine okv_bind (vfh_rabR σ0 _ hc) fun r hr => ?_
    obtain ⟨sl, rem⟩ := r
    dsimp only
    split
    · exact okv_returnOk hr
    · exact okv_throw _
  · exact okv_throw _

theorem okv_and {ε α : Type} {σ0 : State Unit} {P Q : α → Prop} {m : NonDetE (State Unit) ε α}
    (h1 : OkV σ0 P m) (h2 : OkV σ0 Q m) : OkV σ0 (fun a => P a ∧ Q a) m :=
  fun s hs a s' h => ⟨(h1 s hs a s' h).1, (h1 s hs a s' h).2, (h2 s hs a s' h).2⟩

/-- The facts a looked-up cap root carries. -/
abbrev CRoot (σ0 : State Unit) (c : Cap) : Prop := CnOk σ0 c ∧ RootSl σ0 c

theorem vfh_croot_of {σ0 : State Unit} (hd : CnDom σ0) {s : CslotPtr} {c : Cap}
    (h : capOpt (σ0.kheap s.1) s.2 = some c) : CRoot σ0 c := ⟨hd s c h, vfh_rootSl_of h⟩

/-- **A target slot** is no fault-handler slot and its CNode is `DRef`. -/
theorem vfh_lookupTargetSlotR (σ0 : State Unit) (hd : CnDom σ0) (c : Cap) (ptr : CapRef) (depth : Nat)
    (hc : CRoot σ0 c) :
    OkV σ0 (fun sl : CslotPtr => ¬ vfh_Bad σ0 sl ∧ DRef σ0 sl.1) (lookupTargetSlot (Z := Unit) c ptr depth) := by
  unfold lookupTargetSlot
  refine okv_mono (okv_and (vfh_lookupSlotForCnodeOp σ0 hd false c ptr depth hc.1)
    (vfh_lookupSlotForCnodeOpR σ0 false c ptr depth hc.2)) fun sl h => ⟨vfh_notBad_cnFull h.1, h.2⟩

/-- The node cap of an untyped retype / DeriveSubframe: the root or a slot cap. -/
theorem vfh_okv_nodeCap (σ0 : State Unit) (hd : CnDom σ0) (root : Cap) (hr : CRoot σ0 root) (i : CapRef) (d : Nat) :
    OkV σ0 (CRoot σ0) (if d = 0 then NonDetE.returnOk root else do
      let sl ← lookupTargetSlot (Z := Unit) root i d
      NonDetE.liftE (getCap sl) : SEMonad Unit Cap) := by
  split
  · exact okv_returnOk hr
  · exact okv_bind (vfh_lookupTargetSlotR σ0 hd root i d hr) fun sl _ =>
      okv_mono (vfh_okv_getCap sl) fun c h => vfh_croot_of hd h

theorem vfh_okv_subframeNode (σ0 : State Unit) (hd : CnDom σ0) (root : Cap) (hr : CRoot σ0 root) (i d : Data) :
    OkV σ0 (CRoot σ0) (subframeNode (Z := Unit) root i d) := by
  unfold subframeNode
  split
  · exact okv_returnOk hr
  · exact okv_bind (vfh_lookupTargetSlotR σ0 hd root _ _ hr) fun sl _ =>
      okv_mono (vfh_okv_getCap sl) fun c h => vfh_croot_of hd h

/-! ## Slots of a full CNode -/

theorem vfh_natToCref_len (r k : Nat) : (natToCref r k).length = 64 - (64 - r) := by
  simp [natToCref, toBl, wordBits]

/-- **Slot `natToCref r k` of a full CNode of radix `r` is no fault-handler slot.** -/
theorem vfh_natToCref_notBad {σ : State Unit} {p : ObjRef} {r : Nat} (h : CnFull σ p r) (k : Nat) :
    ¬ vfh_Bad σ (p, natToCref r k) := by
  rintro ⟨e, h6⟩
  have hl := vfh_natToCref_len r k
  dsimp only at e h6
  rw [e, vfh_len3] at hl
  exact h (tcbCnodeIndex 6) (by rw [vfh_len6]; omega) h6

theorem vfh_the_mem_fst {ex : List (Cap × CslotPtr)} {i : Nat} (hi : i < (ex.map Prod.fst).length) :
    ∃ p ∈ ex, p.1 = the (ex.map Prod.fst)[i]? := by
  have hm := vfh_the_mem hi
  obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
  exact ⟨p, hp, e⟩

/-! ## The untyped decode -/

/-- What a retype perform needs from its decode. -/
def VUt (σ0 : State Unit) : UntypedInvocation → Prop
  | .retype _ _ _ _ _ _ slots _ => ∀ d ∈ slots, ¬ vfh_Bad σ0 d ∧ DRef σ0 d.1

theorem vfh_okv_ite_ok_bind {ε β : Type} {σ0 : State Unit} {Pr : β → Prop} (c : Prop) [Decidable c] (e : ε)
    {g : Unit → NonDetE (State Unit) ε β} (hg : c → OkV σ0 Pr (g ())) :
    OkV σ0 Pr ((if c then NonDetE.returnOk () else NonDetE.throwError e) >>= g) := by
  split
  · rename_i h; exact okv_returnOk_bind (hg h)
  · exact okv_bind (Q := fun _ => False) (okv_throw _) fun _ h => h.elim

theorem vfh_okv_isCn_bind {ε β : Type} {σ0 : State Unit} {Pr : β → Prop} (nc : Cap) (e : ε)
    {g : Unit → NonDetE (State Unit) ε β} (hg : isCnodeCap nc = true → OkV σ0 Pr (g ())) :
    OkV σ0 Pr ((if isCnodeCap nc = true then NonDetE.returnOk () else NonDetE.throwError e) >>= g) :=
  vfh_okv_ite_ok_bind _ e hg

theorem vfh_vut_slots {σ0 : State Unit} {nc : Cap} (hn : CRoot σ0 nc) (hcn : isCnodeCap nc = true)
    (ks : List Nat) :
    ∀ d ∈ (ks.map (natToCref (Fl4Spec.bitsOf nc))).map (fun cref => (objRefOf nc, cref)),
      ¬ vfh_Bad σ0 d ∧ DRef σ0 d.1 := by
  cases nc with
  | cnodeCap p r g =>
    intro d hd
    simp only [List.map_map, List.mem_map, Function.comp] at hd
    obtain ⟨k, -, rfl⟩ := hd
    exact ⟨vfh_natToCref_notBad (hn.1 p r g rfl) k, hn.2 p r g rfl⟩
  | _ => simp [isCnodeCap] at hcn

set_option maxHeartbeats 8000000 in
theorem vfh_okv_decodeUntyped (σ0 : State Unit) (hd : CnDom σ0) (label : Data) (args : List Data)
    (slot : CslotPtr) (cap : Cap) (ex : List Cap) (hex : ∀ c ∈ ex, CRoot σ0 c) :
    OkV σ0 (VUt σ0) (decodeUntypedInvocationWith (Z := Unit) fl4ObjBitsApi label args slot cap ex) := by
  unfold decodeUntypedInvocationWith
  repeat' (first
    | (refine okv_bind (vfh_okv_nodeCap σ0 hd _ (hex _ (vfh_the_mem (by omega))) _ _) fun nodeCap hnode => ?_)
    | (refine vfh_okv_whenE_bind _ _ fun _ => ?_)
    | exact okv_throw _
    | exact okv_bind (Q := fun _ => False) (okv_throw _) fun _ h => h.elim
    | exact vfh_okv_liftE_fail
    | (refine okv_returnOk_bind ?_)
    | (refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_)
    | split
    | (apply okv_ite))
  all_goals
    refine okv_returnOk ?_
    exact vfh_vut_slots hnode (by assumption) _

/-! ## The arch decode -/

def VPg (σ0 : State Unit) : PageInvocation → Prop
  | .pageMap c sl _ _ => ¬ vfh_Bad σ0 sl ∧ CnOk σ0 c
  | .pageUnmap _ sl => ¬ vfh_Bad σ0 sl
  | _ => True

def VPt (σ0 : State Unit) : PageTableInvocation → Prop
  | .pageTableMap c sl _ _ _ => ¬ vfh_Bad σ0 sl ∧ CnOk σ0 c
  | .pageTableUnmap _ sl => ¬ vfh_Bad σ0 sl

def VPd (σ0 : State Unit) : PageDirectoryInvocation → Prop
  | .pageDirectoryMap c sl _ _ _ => ¬ vfh_Bad σ0 sl ∧ CnOk σ0 c
  | .pageDirectoryUnmap _ sl => ¬ vfh_Bad σ0 sl

def VPdpt (σ0 : State Unit) : PdptInvocation → Prop
  | .pdptMap c sl _ _ _ => ¬ vfh_Bad σ0 sl ∧ CnOk σ0 c
  | .pdptUnmap _ sl => ¬ vfh_Bad σ0 sl

def VIoC (σ0 : State Unit) : IoPortControlInvocation → Prop
  | .ioPortControlInvocation _ _ d _ => ¬ vfh_Bad σ0 d

/-- MakePool: the target slot and its CNode's slot reference. -/
def VMp (σ0 : State Unit) : AsidControlInvocation → Prop
  | .makePool _ slot _ _ => ¬ vfh_Bad σ0 slot ∧ DRef σ0 slot.1

def VArchS (σ0 : State Unit) : ArchInvocation → Prop
  | .invokePageTable i => VPt σ0 i
  | .invokePageDirectory i => VPd σ0 i
  | .invokePDPT i => VPdpt σ0 i
  | .invokePage i => VPg σ0 i
  | .invokeASIDControl i => VMp σ0 i
  | .invokeIOPortControl i => VIoC σ0 i
  | _ => True

/-- What an arch perform needs from its decode. -/
def VArch (σ0 : State Unit) : Fl4ArchInvocation → Prop
  | .spec i => VArchS σ0 i
  | .deriveSubframe iv => ∀ d ∈ iv.dests, ¬ vfh_Bad σ0 d
  | _ => True

theorem vfh_dests {σ0 : State Unit} {p : ObjRef} {r : Nat} (h : CnFull σ0 p r) (ks : List Nat) :
    ∀ d ∈ ks.map (fun i => (p, natToCref r i)), ¬ vfh_Bad σ0 d := by
  intro d hd
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hd
  exact vfh_natToCref_notBad h k

set_option maxHeartbeats 8000000 in
theorem vfh_okv_deriveSubframe (σ0 : State Unit) (hd : CnDom σ0) (args : List Data) (cte : CslotPtr)
    (cap : ArchCap) (ex : List (Cap × CslotPtr)) (hex : ∀ p ∈ ex, CRoot σ0 p.1) :
    OkV σ0 (fun iv => VArch σ0 (.deriveSubframe iv)) (decodeDeriveSubframe (Z := Unit) args cte cap ex) := by
  unfold decodeDeriveSubframe
  repeat' (first
    | (refine okv_bind (vfh_okv_subframeNode σ0 hd _ (hex _ (vfh_the_mem (by omega))) _ _) fun nc hnc => ?_)
    | (rename_i heq; subst heq)
    | exact okv_returnOk (vfh_dests (hnc.1 _ _ _ rfl) _)
    | (refine vfh_okv_whenE_bind _ _ fun _ => ?_)
    | exact okv_throw _
    | exact vfh_okv_liftE_fail
    | (refine okv_returnOk_bind ?_)
    | (refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_)
    | split
    | (apply okv_ite))

set_option maxHeartbeats 16000000 in
theorem vfh_okv_archDecode (σ0 : State Unit) (hd : CnDom σ0) (label : Data) (args : List Data) (xs : CapRef)
    (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) (hnb : ¬ vfh_Bad σ0 cte)
    (hex : ∀ p ∈ ex, CRoot σ0 p.1) :
    OkV σ0 (VArchS σ0) (archDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  have hexm : ∀ c ∈ ex.map Prod.fst, CRoot σ0 c := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    exact hex p hp
  cases cap <;> simp only [archDecodeInvocation, decodePageInvocation, decodePageTableInvocation,
    decodePageDirectoryInvocation, decodePdptInvocation, decodeIoportControlInvocation, decodePortInvocation]
  all_goals repeat' (first
    | (refine okv_bind (vfh_lookupTargetSlotR σ0 hd _ _ _ (hex _ (vfh_the_mem (by omega)))) fun sl hsl => ?_)
    | (refine okv_bind (vfh_lookupTargetSlotR σ0 hd _ _ _ (hexm _ (vfh_the_mem (by omega)))) fun sl hsl => ?_)
    | exact okv_returnOk trivial
    | exact okv_returnOk hnb
    | exact okv_returnOk ⟨hnb, vfh_arch_ok _⟩
    | exact okv_returnOk hsl
    | exact okv_returnOk hsl.1
    | exact okv_throw _
    | exact vfh_okv_liftE_fail
    | (refine okv_returnOk_bind ?_)
    | (refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_)
    | split
    | (apply okv_ite))

set_option maxHeartbeats 8000000 in
theorem vfh_okv_fl4ArchDecode (σ0 : State Unit) (hd : CnDom σ0) (label : Data) (args : List Data) (xs : CapRef)
    (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) (hnb : ¬ vfh_Bad σ0 cte)
    (hex : ∀ p ∈ ex, CRoot σ0 p.1) :
    OkV σ0 (VArch σ0) (fl4ArchDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  unfold fl4ArchDecodeInvocation
  split
  all_goals repeat' (first
    | (exact vfh_okv_liftME (vfh_okv_archDecode σ0 hd label args xs cte _ ex hnb hex))
    | (exact vfh_okv_liftME (vfh_okv_deriveSubframe σ0 hd args cte _ ex hex))
    | (exact vfh_okv_liftME (okv_mono (okv_frame fun v => by hv_auto) fun _ _ => trivial))
    | (apply okv_ite))

/-! ## The dispatcher -/

/-- **What a perform needs from its decode** (vfh1..vfh3). -/
def VInv (σ0 : State Unit) : Fl4Invocation → Prop
  | .invokeUntyped ui => VUt σ0 ui
  | .invokeTCB i => VTcb i
  | .invokeCNode i => VCn σ0 i
  | .invokeIRQControl i => VFl4IrqC σ0 i
  | .invokeIRQHandler i => VIh σ0 i
  | .invokeArchObject a => VArch σ0 a
  | _ => True

/-- An `OkDAt` fact of a frame is an `OkV` fact. -/
theorem vfh_okv_of_okd {ε α : Type} {σ0 : State Unit} {Pr : α → Prop} {m : NonDetE (State Unit) ε α}
    (hf : ∀ v, IKHE (fun s => hV s = v) m) (hp : ∀ s, OkDAt s (fun _ a => Pr a) m) : OkV σ0 Pr m :=
  fun s hs a s' h => ⟨(hf (hV s) s rfl _ h).trans hs, hp s a s' h⟩

set_option maxHeartbeats 8000000 in
/-- **Every decoded invocation satisfies `VInv`**, given the shell's lookups:
the invoked slot holds the invoked cap and every extra cap is in its slot. -/
theorem vfh_okv_fl4Decode (σ0 : State Unit) (hv : VfhV σ0) (hd : CnDom σ0) (fp : Bool) (label : Data)
    (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr))
    (buf : Option ObjRef) (hc : capOpt (σ0.kheap sl.1) sl.2 = some cap)
    (hex : ∀ p ∈ ex, capOpt (σ0.kheap p.2.1) p.2.2 = some p.1) :
    OkV σ0 (VInv σ0) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  have hexr : ∀ p ∈ ex, CRoot σ0 p.1 := fun p hp => vfh_croot_of hd (hex p hp)
  have hexm : ∀ c ∈ ex.map Prod.fst, CRoot σ0 c := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    exact hexr p hp
  cases cap with
  | untypedCap d p n f =>
    unfold fl4DecodeInvocation
    exact vfh_okv_liftME (vfh_okv_decodeUntyped σ0 hd label args sl _ _ hexm)
  | cnodeCap r b g =>
    unfold fl4DecodeInvocation
    exact okv_ite _ (okv_throw _) (vfh_okv_liftME (vfh_okv_decodeCnode σ0 hd label args _ _ (hd _ _ hc)
      fun c hc' => (hexm c hc').1))
  | irqControlCap =>
    unfold fl4DecodeInvocation
    exact vfh_okv_liftME (vfh_okv_decodeIrqControl σ0 hd _ label args sl _ fun c hc' => (hexm c hc').1)
  | irqHandlerCap irq =>
    unfold fl4DecodeInvocation
    exact vfh_okv_liftME (vfh_okv_of_okd (fun v => by hv_auto) fun s => vfh_okd_decodeIrqHandler σ0 label irq ex s)
  | archObjectCap ac =>
    unfold fl4DecodeInvocation
    exact vfh_okv_liftME (vfh_okv_fl4ArchDecode σ0 hd label args ci sl ac ex
      (vfh_notBad_old hv hc (vfh_not_arch ac)) hexr)
  | threadCap t =>
    unfold fl4DecodeInvocation fl4DecodeTcbInvocation
    refine okv_ite _ (okv_throw _) ?_
    repeat' (first
      | (exact vfh_okv_liftME (okv_mono (okv_frame fun v => by hv_auto) fun _ _ => trivial))
      | (exact vfh_okv_liftME (vfh_okv_of_okd (fun v => by hv_auto) fun s =>
          vfh_okd_decodeTcb label args _ sl ex s))
      | (apply okv_ite)
      | split)
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact vfh_okv_liftME (okv_mono (okv_frame fun v => by hv_auto) fun _ _ => trivial))
      | (apply okv_ite)
      | split)

end

end Fl4Proofs.P3.SInv
