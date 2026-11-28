/-
P3 (p3J gen 47): **the CNode cap's decode leaf at stable ghosts at Revoke (25) and Delete (26), for both classes,
with the stable preempted exit**: the CNode labels closed. FL4 `cnode.rs` `decode` at `CNodeRevoke` /
`CNodeDelete` (`cap_revoke` / `cap_delete`, the deletion loop `rec_delete` with its preemption points) by
CnodeRevoke's `cnode_revoke_refinesW` / `cnode_delete_refinesW` at the invariant `DelE ∧ WJSt` (Ok) /
`DelE ∧ WJStP` (preempted), the stable deletion bundle being P3JDelSp's `delHypsJLMstC` lifted by DelFull's
`delHyp_fullWRZ` / `rppHyp_fullW`; as XTopJointMRCnode's `decode_invocation_cnode_{revoke,delete}JLM`, with the
exits `MidX` / `MidXP` (P3JDelSp's `midX_of_wjst` / `midXP_of_wjstp`).

* **`cn_del_topG`**: XTopJointMRCnode's `cn_del_topJLM` with the Ok / preempted invariants and the exits as
  parameters (as XTopJointMRTcbM's `top_of_instJMG`).
* **`decode_invocation_cnode_revokeJSt`** / **`decode_invocation_cnode_deleteJSt`**: start at `Z.mv G V` (a
  dispatch state), exits `MidX Z` / `MidXP Z`.
* **`decCnDelSt`** (any flags, labels 25 / 26): the dispatch leaf, as P3JThSsp's `decThSspSt`.
* `IsRestCap28`: only Thread caps at `ThHard19` (no CNode label left). `restCap27_of28`, `restCap28_of`.
  **`midDecRest27_of_cnd`** / **`invDecRest27_of_cnd`**, `midDecStWL_of_27` / `invDecStWL_of_27`.
* **`DispStabFootLzu` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap28`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzt_of_Lzu`** (under the tops' platform facts and `IrqPlatK`), **`dispStabFootLzu_of_Lzt`**
  (unconditional); top **`kernel_entry_runMcWKR_sysLzu`** (globals verbatim as `_sysLzt`).

Premise honesty: `DispStabFootLzu`'s decode fields are `DispStabFootLzt`'s at the smaller antecedent
(`IsRestCap28 → IsRestCap27`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzu` [J]; globals as `_sysLzt`. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThIns
import Fl4Proofs.P3.XTopJointMRCnode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P1
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **A Delete's or Revoke's outcome at `DelE ∧ W` / `DelE ∧ Wp`, the exits as parameters**
(XTopJointMRCnode's `cn_del_topJLM`; module docstring). -/
theorem cn_del_topG {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    [VxE Z] {kb : U64} {K : Nat} {blk call don : Bool} {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Xo Xp : S → A → Fl4Spec.State Unit → Prop}
    (hw : ∀ s a σ G, W s a σ G → WJR (L := L) arI AR Z H Cs kb s a σ G)
    (hwx : ∀ s a σ G, W s a σ G → Xo s a σ)
    (hwp : ∀ s a σ G, Wp s a σ G → WJP (L := L) arI AR Z H Cs kb s a σ G ∧ Xp s a σ) (hX0 : Xo s ar σ)
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : PInvPostW (L := L) Z.th σ Z.G m (fun s a σ G => DelE (L := L) Z.th K s σ ∧ W s a σ G)
      (fun s a σ G => DelE (L := L) Z.th K s σ ∧ Wp s a σ G) s ar res) :
    TopPostDMXP (L := L) Xo Xp σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  rcases hq with ⟨e, rfl, rfl, rfl, e', h1, h2⟩ |
    ⟨inv, hrun, σ1, hst, σ', G', hcase, hCR', hFI', -, hE'⟩
  · have hne : e ≠ .Preempted := by rintro rfl; cases e' <;> exact h2.elim
    refine Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ?_⟩
    simp only [core.result.Result.Err.injEq, hne, if_false]
    exact hX0
  · rcases hcase with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · obtain ⟨V, Ac', Lst', D', J', -⟩ := hw _ _ _ _ hE'.2
      have hX' := J'.xtop
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, G', Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ?_⟩
      simp only [reduceCtorEq, if_false]
      exact hwx _ _ _ _ hE'.2
    · obtain ⟨⟨-, -, -, -, -, -, hDom, hMO⟩, hPre⟩ := hwp _ _ _ _ hE'.2
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.error (), σ'),
        mem_bindE_err hx, ⟨Z.th, G', Or.inr ⟨rfl, rfl⟩, J.xtop.rel.1, hCR', hFI', hDom, hMO⟩, ?_⟩
      simp only [if_true]
      exact hPre

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`XCapP` at stable ghosts at the Revoke label** (25; module docstring). -/
theorem decode_invocation_cnode_revokeJSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    {G : MdbGhost} {V : XVs} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s ar σ) [VxE (Z.mv G V)] (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ) (hMV : MRV MR ar σ) (hC : SInvCk.CKI σ) (hRN : RrNs σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s) (MidXP (L := L) arI AR MR Z H Cs s) s ar σ
      fl4_abi.label.CNodeRevoke length slot (.CNode p r gs g) blk call don fp buf extra slbl (args.map UScalar.bv) ci
      sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  have hfew : psiD (L.mem s) G < 2 ^ 64 - 1 := by
    have := hDE.2.1 G hM
    omega
  have hH := delHypsJLMstC (L := L) (st := st) hT hARI.toARKeep hticks hnd hMT.toC hKD hPA hARI.toMask (Z.mv G V) H Cs (L.ksb s) rfl s
  have hJD := delHyp_fullWRZ (L := L) arI _ _ _ _ _ Z.th hP (finalHyp_full (L := L) Z.th hP) hH K hK hK6
  have hX0 : MidX (L := L) arI AR MR Z H Cs s s ar σ := ⟨JStab.mv J.stab, hMV.1, P1.WritesIn.refl _ _⟩
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_revoke_refinesW arI Z.th s ar σ G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb
      (fun s1 a1 σ1 G1 => DelE (L := L) Z.th K s1 σ1 ∧
        WJSt (L := L) arI AR MR (Z.mv G V) H Cs s (L.ksb s) s1 a1 σ1 G1)
      (fun s1 a1 σ1 G1 => DelE (L := L) Z.th K s1 σ1 ∧
        WJStP (L := L) arI AR MR (Z.mv G V) H Cs s (L.ksb s) s1 a1 σ1 G1)
      psiD psiD_slotsSame hJD (rppHyp_fullW arI _ _ Z.th K hH.pp)
      (fun s1 σ1 hs1 hS hst => ⟨delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) hst),
        restartWJSt hMT.toC J hni hsg hP0 hLv hMV hC hRN ct hct s1 σ1 hs1 hst⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩) hfew)
      fun res h => cn_del_topG (kb := L.ksb s) (K := K)
        (W := WJSt (L := L) arI AR MR (Z.mv G V) H Cs s (L.ksb s))
        (Wp := WJStP (L := L) arI AR MR (Z.mv G V) H Cs s (L.ksb s))
        (Xo := MidX (L := L) arI AR MR Z H Cs s) (Xp := MidXP (L := L) arI AR MR Z H Cs s)
        J (fun _ _ _ _ h => h.1.1.1.1.1)
        (fun _ _ _ _ h => (midX_of_wjst h).mv)
        (fun _ _ _ _ h => ⟨h.1.1.1.1.1, (midXP_of_wjstp hARI hT hnd hMT hKD hIP hTA hPA h).mv⟩) hX0 h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact hX0

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`XCapP` at stable ghosts at the Delete label** (26; module docstring). -/
theorem decode_invocation_cnode_deleteJSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    {G : MdbGhost} {V : XVs} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s ar σ) [VxE (Z.mv G V)] (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ) (hMV : MRV MR ar σ) (hC : SInvCk.CKI σ) (hRN : RrNs σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s) (MidXP (L := L) arI AR MR Z H Cs s) s ar σ
      fl4_abi.label.CNodeDelete length slot (.CNode p r gs g) blk call don fp buf extra slbl (args.map UScalar.bv) ci
      sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  have hH := delHypsJLMstC (L := L) (st := st) hT hARI.toARKeep hticks hnd hMT.toC hKD hPA hARI.toMask (Z.mv G V) H Cs (L.ksb s) rfl s
  have hJD := delHyp_fullWRZ (L := L) arI _ _ _ _ _ Z.th hP (finalHyp_full (L := L) Z.th hP) hH K hK hK6
  have hX0 : MidX (L := L) arI AR MR Z H Cs s s ar σ := ⟨JStab.mv J.stab, hMV.1, P1.WritesIn.refl _ _⟩
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_delete_refinesW arI Z.th s ar σ G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb
      (fun s1 a1 σ1 G1 => DelE (L := L) Z.th K s1 σ1 ∧
        WJSt (L := L) arI AR MR (Z.mv G V) H Cs s (L.ksb s) s1 a1 σ1 G1)
      (fun s1 a1 σ1 G1 => DelE (L := L) Z.th K s1 σ1 ∧
        WJStP (L := L) arI AR MR (Z.mv G V) H Cs s (L.ksb s) s1 a1 σ1 G1)
      psiD hJD
      (fun s1 σ1 hs1 hS hst => ⟨delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) hst),
        restartWJSt hMT.toC J hni hsg hP0 hLv hMV hC hRN ct hct s1 σ1 hs1 hst⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩))
      fun res h => cn_del_topG (kb := L.ksb s) (K := K)
        (W := WJSt (L := L) arI AR MR (Z.mv G V) H Cs s (L.ksb s))
        (Wp := WJStP (L := L) arI AR MR (Z.mv G V) H Cs s (L.ksb s))
        (Xo := MidX (L := L) arI AR MR Z H Cs s) (Xp := MidXP (L := L) arI AR MR Z H Cs s)
        J (fun _ _ _ _ h => h.1.1.1.1.1)
        (fun _ _ _ _ h => (midX_of_wjst h).mv)
        (fun _ _ _ _ h => ⟨h.1.1.1.1.1, (midXP_of_wjstp hARI hT hnd hMT hKD hIP hTA hPA h).mv⟩) hX0 h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact hX0

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **The CNode cap's decode at a dispatch state at Revoke / Delete, any flags** (module docstring;
as P3JThSsp's `decThSspSt`). -/
theorem decCnDelSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsg : SpecGlob σb)
    (hP0 : PPR0 σb) (hCb : SInvCk.CKI σb) (hRRb : SInvRr.RR σb) (hNSb : NativeScope σb)
    (hMb : MR a' σb.machineState) (hVTb : ValidMachineTime σb) (hVIb : ValidIrqMasks σb)
    {ct : U64} (hct : sched.cur_thread st s' = ok ct)
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
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p r gs g : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.CNode p r gs g))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs) (hl : CnDel info.label)
    (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.CNode p r gs g) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  obtain ⟨sl', hl', hd⟩ := cnode_canon info.label
  refine XCapP.lbl_congr arI (specDec_cnode p r gs g hd) ?_
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .CNode p r gs g := capV_of_capAt hc
  obtain ⟨hwf, hcv⟩ := slot_cap_wf J.xtop hAs hsc
  unfold CnDel at hl
  rcases (show info.label.val = 25 ∨ info.label.val = 26 by omega) with h | h
  · have e25 : info.label = fl4_abi.label.CNodeRevoke := UScalar.eq_of_val_eq (by rw [h, lbl_revoke_val])
    rw [e25]
    exact decode_invocation_cnode_revokeJSt hARI hA hticks hnd hMT hKD hIP hTA hPA s' a' σb J hnib hsg hP0 J.live
      ⟨hMb, hVTb, hVIb⟩ hCb ⟨hRRb, hNSb⟩ sl' (by rw [hl']; simp [cnodeLabelOf, h]) _ buf ct hct argsU hLen hArgs
      p r gs g hwf hcv e exs (cslotAddr sl) bl call don fp ci sl buffer
  · have e26 : info.label = fl4_abi.label.CNodeDelete := UScalar.eq_of_val_eq (by rw [h, lbl_delete_val])
    rw [e26]
    exact decode_invocation_cnode_deleteJSt hARI hA hticks hnd hMT hKD hIP hTA hPA s' a' σb J hnib hsg hP0 J.live
      ⟨hMb, hVTb, hVIb⟩ hCb ⟨hRRb, hNSb⟩ sl' (by rw [hl']; simp [cnodeLabelOf, h]) _ buf ct hct argsU hLen hArgs
      p r gs g hwf hcv e exs (cslotAddr sl) bl call don fp ci sl buffer

end

/-- (p3J gen 47) The caps left after the Revoke / Delete leaf, with the message label: Thread caps only. -/
def IsRestCap28 : capability.Cap → U64 → Prop
  | .Thread _, l => ThHard19 l
  | _, _ => False

theorem restCap27_of28 {cp : capability.Cap} {l : U64} (h : IsRestCap28 cp l) : IsRestCap27 cp l := by
  cases cp
  case Thread => exact h
  all_goals exact False.elim h

theorem restCap28_of {cp : capability.Cap} {l : U64} (h : IsRestCap27 cp l)
    (hS : ¬ ∃ p r gs g, cp = .CNode p r gs g ∧ CnDel l) : IsRestCap28 cp l := by
  cases cp
  case CNode p r gs g => exact hS ⟨p, r, gs, g, rfl, h⟩
  case Thread => exact h
  all_goals exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`MidDecStWL` at `KW ∧ IsRestCap27` from the Revoke / Delete leaf** (module docstring). -/
theorem midDecRest27_of_cnd [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p r gs g, cp = .CNode p r gs g ∧ CnDel info.label
  · obtain ⟨p, r, gs, g, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decCnDelSt hARI hA hticks hnd hMT hKD hIP hTA hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap28_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`InvDecStWL` at `KW ∧ IsRestCap27` from the Revoke / Delete leaf** (module docstring). -/
theorem invDecRest27_of_cnd [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p r gs g, cp = .CNode p r gs g ∧ CnDel info.label
  · obtain ⟨p, r, gs, g, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decCnDelSt hARI hA hticks hnd hMT hKD hIP hTA hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap28_of hW.2 hS⟩

/-- (p3J gen 47) `MidDecStWL` at `KW ∧ IsRestCap27` gives it at `KW ∧ IsRestCap28` (antitone). -/
theorem midDecStWL_of_27 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap27_of28 hW.2⟩

/-- (p3J gen 47) `InvDecStWL` at `KW ∧ IsRestCap27` gives it at `KW ∧ IsRestCap28` (antitone). -/
theorem invDecStWL_of_27 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap27_of28 hW.2⟩

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

/-- (p3J gen 47) **`DispStabFootLzu` [J]**: `DispStabFootLzt` with `invDecRest` / `midDecRest` restricted to
`IsRestCap28` (`IsRestCap27` minus the CNode caps at Revoke / Delete; module docstring). -/
structure DispStabFootLzu (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzt.invDecRest` at `KW ∧ IsRestCap28`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzt.midDecRest` at `KW ∧ IsRestCap28`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzt.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzt.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 47) **`DispStabFootLzu → DispStabFootLzt`** under the tops' platform facts and `IrqPlatK` (module
docstring). -/
theorem dispStabFootLzt_of_Lzu [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzu (L := L) arI AR MR s a σ) :
    DispStabFootLzt (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest27_of_cnd hARI hA ⟨hmax, htu⟩ hnd (MachPlatF.toT hM hIp) hKD hIA hT ⟨hPAi, hT.mb⟩ hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest27_of_cnd hARI hA ⟨hmax, htu⟩ hnd (MachPlatF.toT hM hIp) hKD hIA hT ⟨hPAi, hT.mb⟩ hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 47) **`DispStabFootLzt → DispStabFootLzu`** (the honesty claim: `DispStabFootLzu` is implied). -/
theorem dispStabFootLzu_of_Lzt {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzt (L := L) arI AR MR s a σ) : DispStabFootLzu (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_27 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_27 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzu` only** (`hLzu` [J];
globals verbatim as `_sysLzt`; module docstring). -/
theorem kernel_entry_runMcWKR_sysLzu [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzu : DispStabFootLzu (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzt hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzt_of_Lzu hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hLzu)

end

end Fl4Proofs.P3.Mc
