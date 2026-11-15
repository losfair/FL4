/-
P3 (DESIGN.md §9): **the MDB invariants on the cap branches** (`DecOKM`,
`DecOKDM`; TopM): the domain cap, the IO port caps, IO port control and IRQ
control (TopFCaps' with `MdbOKV` for the frame invariant), the CNode caps
(`decode_invocation_cnodeM`) and the untyped caps
(`decode_invocation_untypedM`), from the `MdbStep`s their posts carry.
-/
import Fl4Proofs.P3.TopM
import Fl4Proofs.P3.TopFCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `liftME` of a decode with a single outcome. -/
theorem topM_of_lift {α : Type} {f : α → Fl4Spec.Fl4Invocation} {m : Fl4Spec.SEMonad Unit α}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f inv)).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
          MdbOKV (L.ksb s) (L.mem res.2.1) G')) :
    TopPostM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f m) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err hr, he⟩
  · exact Or.inr ⟨f inv, DecOut.of_eq (run_liftME_ok hr), rest⟩

/-- Two `liftME`s of a decode with a single outcome. -/
theorem topM_of_lift2 {α β : Type} {f : α → Fl4Spec.Fl4Invocation} {g : β → α} {m : Fl4Spec.SEMonad Unit β}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f (g inv))).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
          MdbOKV (L.ksb s) (L.mem res.2.1) G')) :
    TopPostM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f (Fl4Spec.NonDetE.liftME g m)) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err (run_liftME_err hr), he⟩
  · exact Or.inr ⟨f (g inv), DecOut.of_eq (run_liftME_ok (run_liftME_ok hr)), rest⟩

def PortCPostM (th : TypedHeap) (σ : Fl4Spec.State Unit) (m : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation)
    (s : S) : core.result.Result Unit error.Exc × S × A → Prop
  | (.Err e, s', _) => s' = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e'
  | (.Ok (), s', _) => ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      ∃ σ' G' r, (.ok r, σ') ∈ ((Fl4Spec.archPerformInvocation (Z := Unit) inv).run σ1).1 ∧
        CRel th (L.mem s') σ' G' ∧ FinInv th (L.mem s') σ' G' ∧ MdbOKV (L.ksb s) (L.mem s') G'

/-- From the labels' `PortPost`: a port invocation that changed no slot. -/
theorem PortPost.toCM {th : TypedHeap} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G) {ct : U64} (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) {m : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation} {Q : Fl4Spec.ArchInvocation → S → A → Prop}
    (hQ : ∀ inv s' a', Q inv s' a' → SlotsSame th (L.mem s) (L.mem s') ∧
      ∃ port d, inv = .invokeIOPort (.ioPortInvocation port d))
    {res : core.result.Result Unit error.Exc × S × A} (h : PortPost σ m s ar Q res) :
    PortCPostM (L := L) th σ m s res := by
  obtain ⟨r, s', a'⟩ := res
  cases r with
  | Err e => obtain ⟨h1, -, e', h2, h3⟩ := h; exact ⟨h1, e', h2, h3⟩
  | Ok u =>
    obtain ⟨inv, hrun, hq⟩ := h
    obtain ⟨hS, port, d, rfl⟩ := hQ _ _ _ hq
    obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
    obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
    obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hS (t := ct.bv) hkt .restart
    obtain ⟨rr, ms, hmem⟩ := port_perform_ex σ1 port d
    refine ⟨_, hrun, σ1, by rw [hcur]; exact hst1, _, G, rr, hmem,
      ⟨hR1.of_kheap rfl, hV1, hM1, hC1.of_cdt rfl rfl, MdbInv.of_same hM hI hS⟩,
      hFI.of_same hM hS ((ksub_of_eq (setThreadState_nks _ _) hst1).trans (KSub.of_kheap rfl)), MdbOKV.of_same hM hS hFR⟩

theorem ioport_decode_refinesM (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536) (call : Bool)
    (hcall : 64 ≤ lbl.val ∧ lbl.val ≤ 66 → call = false)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a'))
    (hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a') :
    ioport.decode st arI s ar lbl length (.IoPort first last 0#u64) call buf ⦃ res =>
      PortCPostM (L := L) th σ (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
        (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val))) s res ⦄ := by
  obtain ⟨hlI, hlO, hlX⟩ := hlbl
  by_cases hI : 64 ≤ lbl.val ∧ lbl.val ≤ 66
  · rw [hcall hI]
    refine WP.spec_mono (port_in_refines arI th hP s ar σ lbl hI slbl (hlI hI) length buf ct hct args hlen hargs
      htcb hact first last hfl hl16 hin) (fun res h => PortPost.toCM hCR hFI hFR hcur htcb ?_ h)
    rintro inv s' a' ⟨port, -, rfl, -, hS⟩
    exact ⟨hS, _, _, rfl⟩
  by_cases hO : 67 ≤ lbl.val ∧ lbl.val ≤ 69
  · refine WP.spec_mono (port_out_refines arI th hP s ar σ lbl hO slbl (hlO hO) length buf ct hct args hlen hargs
      htcb hact first last hfl hl16 call hout) (fun res h => PortPost.toCM hCR hFI hFR hcur htcb ?_ h)
    rintro inv s' a' ⟨port, data, raw, -, -, rfl, -, hS⟩
    exact ⟨hS, _, _, rfl⟩
  have hX : lbl.val < 64 ∨ 69 < lbl.val := by omega
  exact WP.spec_mono (port_other_refines arI s ar σ lbl hX slbl (hlX hX) length buf ct hct _ first last call)
    (fun res h => PortPost.toCM hCR hFI hFR hcur htcb (fun _ _ _ h => h.elim) h)


theorem decode_invocation_ioportM (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536) (call : Bool)
    (hcall : 64 ≤ lbl.val ∧ lbl.val ≤ 66 → call = false)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a'))
    (hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a')
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length slot (.IoPort first last 0#u64) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  unfold DecOKM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (ioport_decode_refinesM arI th hP s ar σ G hCR hFI hFR lbl slbl hlbl length buf ct hct args hlen
    hargs hcur htcb hact first last hfl hl16 call hcall hin hout) ?_
  rintro ⟨r0, s', a'⟩ hq
  apply topM_of_lift2 (f := Fl4Spec.Fl4Invocation.invokeArchObject) (g := Fl4Spec.Fl4ArchInvocation.spec)
  cases r0 with
  | Err e => obtain ⟨rfl, e', h1, h2⟩ := hq; exact Or.inl ⟨e, rfl, rfl, e', h1, h2⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', rr, hx, hCR', hF, hFr⟩ := hq
    exact Or.inr ⟨inv, hrun, σ1, hst, (.ok rr, σ'), hx, th, G', Or.inl ⟨rfl, rr, rfl⟩, hP, hCR', hF, hFr⟩

theorem decode_invocation_domainDM (hcfg : DomConfig) (th : TypedHeap) (hP : Placed th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 excs)
    (hSet : DomSetHyp (L := L) th s σ ct) (hRes : DomResHyp (L := L) th s σ ct)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKDM (L := L) arI s ar σ lbl length slot .Domain blk call don fp buf extra slbl (args.map UScalar.bv) ci sl
      excs buffer := by
  unfold DecOKDM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (domain_decode_refines hcfg th hP s σ G hCR hFI hDR ct hct hcur htcb hact hkf hka hksO hactK
      lbl slbl hlbl length buf args hlen hargs extra x0 hx0 excs hex hSet hRes) ?_
    rintro ⟨r0, s'⟩ hq
    simp only [uncurry_apply_pair]
    rw [WP.spec_ok]
    rcases hq with ⟨e, he, hs', e', h1, h2⟩ | ⟨he, inv, hrun, σ1, hst, y, hy, hS', hCR', hFI', hkb', hDR'⟩
    · exact Or.inl ⟨e, he, hs', e', run_liftME_err h1, Or.inl h2⟩
    · have hm : ((.ok [], y.2) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
          ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain inv)).run σ1).1 := by
        show _ ∈ ((Fl4Spec.NonDetE.liftE (do Fl4Spec.invokeDomain (Z := Unit) inv; return ([] : List Fl4Spec.Data))).run
          σ1).1
        exact mem_liftE (x := ([], y.2)) (mem_bind_nd hy rfl)
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], y.2), hm, th, G, Or.inl ⟨he, [], rfl⟩, hP, hCR', hFI',
        hDR', by rw [hkb']; exact MdbOKV.of_same hCR.2.2.1 hS' hFR⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩


theorem decode_invocation_ioport_controlM (th : TypedHeap) (hP : Placed th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hL : IoLayout th (L.ksb s))
    (hIo : IoRel (L.mem s) (L.ksb s) σ) (hPA : IoPortsAlloc (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer := by
  unfold DecOKM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (ioport_control_decode_refines arI th hP s ar σ G hCR hL hIo hPA hFI hFR lbl slbl hlbl length buf
    ct hct args hlen hargs hcur htcb hact hact3 extra x0 hx0 _ hex hps hls hsrcC .ioPortControlCap) ?_
  rintro ⟨r0, s', a'⟩ hq
  apply topM_of_lift2 (f := Fl4Spec.Fl4Invocation.invokeArchObject) (g := Fl4Spec.Fl4ArchInvocation.spec)
  cases r0 with
  | Err e => obtain ⟨rfl, e', h1, h2⟩ := hq; exact Or.inl ⟨e, rfl, rfl, e', h1, h2⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', rr, hx, hCR', -, hF, -, hFr⟩ := hq
    exact Or.inr ⟨inv, hrun, σ1, hst, (.ok rr, σ'), hx, th, G', Or.inl ⟨rfl, rr, rfl⟩, hP, hCR', hF, hFr⟩


theorem decode_invocation_irq_controlM (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hAR : ArchIrqRel arI ar σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer := by
  unfold DecOKM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have e : specDec fp slbl (args.map UScalar.bv) ci (ps.bv, idxs) .IrqControl excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeIRQControl
        (Fl4Spec.decodeFl4IrqControl (decide (lbl.val = 72)) slbl (args.map UScalar.bv) (ps.bv, idxs)
          (excaps.map Prod.fst)) := by
    rw [hrm]; rfl
  rw [e]
  refine WP.spec_mono (irq_control_decode_refines arI th hP s ar σ G hCR hL hIR hHA hFI hFR lbl slbl hlbl length buf ct
    hct args hlen hargs hcur htcb hact hact2 extra x0 hx0 _ hex hps hls hsrcC nA hnum hnA hmask hAR) ?_
  rintro ⟨r0, s', a'⟩ hq
  apply topM_of_lift
  cases r0 with
  | Err e => obtain ⟨rfl, e', h1, h2⟩ := hq; exact Or.inl ⟨e, rfl, rfl, e', h1, h2⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, hCR', -, hF, -, hFr⟩ := hq
    exact Or.inr ⟨inv, hrun, σ1, hst, (.ok [], σ'), mem_bindE_ok hx (Set.mem_singleton _), th, G',
      Or.inl ⟨rfl, [], rfl⟩, hP, hCR', hF, hFr⟩


/-- **A CNode cap** (`cnode_decode_refines`). -/
theorem decode_invocation_cnodeM (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hI : MdbInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hEp : CancelEpHyp (L := L) th s σ)
    (E : S → Fl4Spec.State Unit → Prop) (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHyp (L := L) arI μ th E) (hPP : RPPHyp (L := L) arI th E)
    (hE : ∀ s1 σ1, SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → E s1 σ1)
    (hEF : ∀ s1 σ1 G1, CRel th (L.mem s1) σ1 G1 → E s1 σ1 → FinInv th (L.mem s1) σ1 G1)
    (hfew : μ (L.mem s) G < 2 ^ 64 - 1)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  unfold DecOKM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (cnode_decode_refines arI th s ar σ G hR hV hP hM hC lbl slbl hlbl length buf ct hct args
      hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra x0 x1 hx0 hx1 _ hex hI hFI hact hcur htcb hEp E μ hμ hD hPP hE hEF hfew) ?_
    rintro ⟨r0, s', a'⟩ hq
    apply topM_of_lift (f := Fl4Spec.Fl4Invocation.invokeCNode)
    rcases hq with ⟨e, he, rfl, e', he1, he2⟩ | ⟨inv, hrun, σ1, hst, σ', G', hcase, hCR, hF, hSt⟩
    · exact Or.inl ⟨e, he, rfl, e', he1, Or.inl he2⟩
    · have hMO' : MdbOKV (L.ksb s) (L.mem s') G' := hSt.okv hMO
      refine Or.inr ⟨inv, hrun, σ1, hst, ?_⟩
      rcases hcase with ⟨he, hx⟩ | ⟨he, hx⟩
      · exact ⟨(.ok [], σ'), mem_bindE_ok hx (Set.mem_singleton _), th, G', Or.inl ⟨he, [], rfl⟩, hP, hCR, hF, hMO'⟩
      · exact ⟨(.error (), σ'), mem_bindE_err hx, th, G', Or.inr ⟨he, rfl⟩, hP, hCR, hF, hMO'⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **An untyped cap** (`untyped_retype_refines_fl4P`, every object type,
resets included). -/
theorem decode_invocation_untypedM (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G) (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hnt : ∀ x, args.head? = some x → x.val ≤ 13)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hactZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hsb4 : 4 ≤ sb.val) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hPP : ∀ k0 v0 : U64, PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
      L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = v0))
    (hRst : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val ≠ 0 →
      (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
      (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
      ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val))
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pp.bv, idx)) (.Untyped p sb fi dev) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci (pp.bv, idx) excaps buffer := by
  unfold DecOKM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (untyped_retype_refines_fl4P arI th s ar σ G hR hV hP hM hC hI hU horig lbl slbl hlbl length
    buf ct hct args hlen hargs hnt hcur htcb hact hpp hidx hcap hpal hpfit hfi hhigh hactZ hfree hzero hsb4 hN hns
    hrcb hppS hPP hRst extra x0 hx0 _ hex hfan hDWal hDWobj hDWreg hDWne hhead hgpm hga hgf hgreg) ?_
  rintro res hq
  apply topM_of_lift (f := Fl4Spec.Fl4Invocation.invokeUntyped)
  rcases hq with ⟨e, e', rfl, h1, h2⟩ | ⟨inv, hrun, σ1, hst, -, ev, σ', G', th', hcase, ⟨⟨y1, y2⟩, hy, hy1, hK⟩,
    hP', hR', hV', hM', hC', hI', -, hSt, hFin⟩
  · exact Or.inl ⟨e, rfl, rfl, e', h1, Or.inl h2⟩
  · refine Or.inr ⟨inv, hrun, σ1, hst, ?_⟩
    simp only at hy1 hK
    subst hy1
    have hCR : CRel th' (L.mem res.2.1) y2 G' :=
      ⟨hR'.of_kheap hK.1, hV', hM', hC'.of_cdt hK.2.1 hK.2.2.1, hI'⟩
    have hF : FinInv th' (L.mem res.2.1) y2 G' :=
      (hFin hFI).of_same hM' (SlotsSame.refl _ _) (KSub.of_kheap hK.1)
    rcases hcase with ⟨he, rfl⟩ | ⟨he, rfl⟩
    · exact ⟨(.ok [], y2), mem_bindE_ok hy (Set.mem_singleton _), th', G', Or.inl ⟨he, [], rfl⟩, hP', hCR, hF, hSt.okv hMO⟩
    · exact ⟨(.error (), y2), mem_bindE_err hy, th', G', Or.inr ⟨he, rfl⟩, hP', hCR, hF, hSt.okv hMO⟩

/-- **An IRQ handler cap** (`irq_handler_decode_refines`). -/
theorem decode_invocation_irq_handlerM (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel th (L.mem s) x0 excaps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length slot (.IrqHandler irq) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  unfold DecOKM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (irq_handler_decode_refines arI th hP hO hPD hK s ar σ G hDS hL hIR lbl slbl hlbl ct hct hcur
    htcb hact hmask irq hirq hok extra x0 hx0 excaps hex hxn) ?_
  rintro ⟨r0, s', a'⟩ hq
  apply topM_of_lift (f := Fl4Spec.Fl4Invocation.invokeIRQHandler)
  cases r0 with
  | Err e => obtain ⟨rfl, e', h1, h2⟩ := hq; exact Or.inl ⟨e, rfl, rfl, e', h1, h2⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, hCR, hF, hSt⟩ := hq
    exact Or.inr ⟨inv, hrun, σ1, hst, (.ok [], σ'), mem_bindE_ok (mem_liftE hx) (Set.mem_singleton _), th, G',
      Or.inl ⟨rfl, [], rfl⟩, hP, hCR, hF, hSt.okv hMO⟩

end

end

end Fl4Proofs.P3
