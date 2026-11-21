/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch18 (a)): **the
frame of `maybe_return_sched_context` at `JAtZR`**, for the SC return of a
blocking notification receive under a pending switch.

* `Sched.maybeReturn_midR`: `maybeReturn_mid` with `CurInvR` in and out
  (under a switch the current thread need not satisfy `CurInv`; when it
  gives its SC back the action becomes `chooseNewThread`).
* Scripted copies (sch9gen/gen.py with root `JAtZ.maybeReturnJQ`, `JAtZ` ->
  `JAtZR`; the copies already in XTopJointJAtZRA (`tcbs_eq`, `idleW_keep`,
  `sc_jcov`, `kw_dbg`, `deadY_tcb`, `ymd`, `sc_out_keep`) dropped): `JAtZR.sc_frame` (with `hcur : CurInvR`),
  `sc_buf`, `sc_apart`, `sc_jpl`, `sc_kern`, `sc_utc`,
  `deadP_sc_stepQm/Q/G`, `deadP_sc_step`, `spec_of_words`,
  `words_of_spec`, `maybeReturnJQ` (with `maybeReturn_midR`). FOLD LATER with
  XTopJointJAtZRA/B if `JAtZ.cur` is ever weakened to `CurInvR`.
-/
import Fl4Proofs.P3.XTopJointJAtZRA
import Fl4Proofs.P3.XTopJointRecvSigRet
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical

noncomputable section

/-- **The mid-entry facts after `maybe_return_sc`** (sch18: `maybeReturn_mid` with
`CurInvR` in and out). -/
theorem maybeReturn_midR {T C : Set U64} {σ σ' : State Unit} {n i t : ObjRef} {y : SchedContext} {m : Nat}
    {x : Tcb} {xn : Notification}
    (hI : Inv σ) (hks : σ.kheap i = some (.schedContext y m)) (hy : y.scTcb = some t)
    (hkt : σ.kheap t = some (.tcb x)) (hxs : x.tcbSchedContext = some i)
    (hkn : σ.kheap n = some (.notification xn)) (hxn : xn.ntfnSc = some i) (hnq : NotQueued σ t)
    (hiC : ∃ q ∈ C, UScalar.bv q = i)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t) (hid : t ≠ σ.idleThread)
    (hcur : CurInvR σ) (hown : CurOwnW T C σ) (hoff : OffOK σ)
    (hact : ActIdle σ) (hcr : CurRunM σ)
    (he : maybeReturnSc (Z := Unit) n t σ = ({((), σ')}, False)) :
    CurInvR σ' ∧ CurOwnW T C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
      CurRunM σ' ∧ FK σ σ' := by
  obtain ⟨σ2, e2, kt, ki, ko, ct, cs, tm, cn, hidl, hisc, rq, a1, b1, -⟩ := maybeReturn_shape hI hkn hkt hks hxs hxn hnq
  have e := the_result e2 he
  subst e
  have hti : t ≠ i := by rintro rfl; rw [hkt] at hks; cases hks
  have nTi : ∀ q (z : Tcb), σ.kheap q = some (.tcb z) → q ≠ i := by
    rintro q z hq rfl; rw [hks] at hq; cases hq
  have nSt : ∀ q (z : SchedContext) m, σ.kheap q = some (.schedContext z m) → q ≠ t := by
    rintro q z m hq rfl; rw [hkt] at hq; cases hq
  have hidi : σ.idleThread ≠ i := by obtain ⟨xi, h1, -⟩ := hact.2; exact nTi _ _ h1
  have hIdle : IdleOK σ' := IdleOK.of hact.2 hidl (ko _ (Ne.symm hid) hidi) (fun h => rq _ h)
  have hAct : ActIdle σ' := by
    refine ⟨fun u hu => ?_, hIdle⟩
    by_cases htc : t = σ.curThread
    · rw [a1 htc] at hu; cases hu
    rw [b1 htc] at hu
    obtain ⟨xu, scp, yu, nu, hku, hsc, hrun, hky, hac, hnr'⟩ := schedulable_inv (hact.1 u hu)
    have hut : u ≠ t := hsa u hu
    have hui : u ≠ i := nTi _ _ hku
    have hst : scp ≠ t := nSt _ _ _ hky
    have hsi : scp ≠ i := by
      rintro rfl
      obtain ⟨y1, n1, h1, h2⟩ := hI.back u xu scp hku hsc
      rw [hks] at h1; cases h1; rw [hy] at h2; cases h2; exact hut rfl
    exact schedulable_of (by rw [ko _ hut hui]; exact hku) hsc hrun (by rw [ko _ hst hsi]; exact hky) hac
      (fun h => hnr' (rq _ h))
  refine ⟨?_, ?_, ?_, hAct, ?_, ⟨cs, hidl, hisc⟩⟩
  · intro hres
    by_cases htc : t = σ.curThread
    · rw [a1 htc] at hres; cases hres
    have hC := hcur (by rw [← b1 htc]; exact hres)
    obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
    obtain ⟨y1, n1, hk1⟩ := hC.sc
    have hct : σ.curThread ≠ t := fun e => htc e.symm
    have hci : σ.curThread ≠ i := nTi _ _ hkc
    have hcst : σ.curSc ≠ t := nSt _ _ _ hk1
    have hcsi : σ.curSc ≠ i := by
      rintro e
      obtain ⟨y2, n2, h1, h2⟩ := hI.back _ xt _ hkc hcs
      rw [e, hks] at h1; cases h1; rw [hy] at h2; cases h2; exact htc rfl
    refine ⟨⟨xt, by rw [ct, ko _ hct hci]; exact hkc, by rw [cs]; exact hcs, hnb⟩,
      ⟨y1, n1, by rw [cs, ko _ hcst hcsi]; exact hk1⟩, fun hne y3 n3 h3 => ?_,
      fun h => hC.notRel (by rw [ct] at h; exact rq _ h)⟩
    rw [cs, hisc] at hne; rw [cs] at h3; rw [ko _ hcst hcsi] at h3
    exact hC.active hne y3 n3 h3
  · rcases hown with ⟨u, hu, xt, hku, hxt, hown, hnr'⟩ | ⟨hcs, hun⟩
    · by_cases hut : UScalar.bv u = t
      · have hku' : σ.kheap t = some (.tcb xt) := by rw [← hut]; exact hku
        rw [hkt] at hku'; cases hku'
        rw [hxs] at hxt; cases hxt
        refine Or.inr ⟨by rw [cs]; exact hiC, fun x' n' h => ?_⟩
        rw [cs, ki] at h; cases h; rfl
      · have hui : UScalar.bv u ≠ i := nTi _ _ hku
        obtain ⟨y1, n1, hk1, -⟩ := hI.back _ xt _ hku hxt
        have hcst : σ.curSc ≠ t := nSt _ _ _ hk1
        have hcsi : σ.curSc ≠ i := by
          rintro e
          have := hown y1 n1 hk1
          rw [e, hks] at hk1; cases hk1; rw [hy] at this; cases this; exact hut rfl
        exact Or.inl ⟨u, hu, xt, by rw [ko _ hut hui]; exact hku, by rw [cs]; exact hxt,
          fun x' n' h => hown x' n' (by rw [cs, ko _ hcst hcsi] at h; exact h),
          fun h0 hm => hnr' (by rw [← cn]; exact h0) (rq _ hm)⟩
    · refine Or.inr ⟨by rw [cs]; exact hcs, fun x' n' h => ?_⟩
      rw [cs] at h
      by_cases e : σ.curSc = i
      · rw [e, ki] at h; cases h; rfl
      by_cases e2 : σ.curSc = t
      · rw [e2, kt] at h; cases h
      rw [ko _ e2 e] at h; exact hun _ _ h
  · intro h0 y1 n1 h1 ha
    rw [cn] at h0 ⊢; rw [tm]
    rw [cs] at h1; rw [cs, hisc] at ha
    by_cases e : σ.curSc = i
    · rw [e, ki] at h1; cases h1
      exact hoff h0 y m (by rw [e]; exact hks) ha
    by_cases e2 : σ.curSc = t
    · rw [e2, kt] at h1; cases h1
    rw [ko _ e2 e] at h1
    exact hoff h0 y1 n1 h1 ha
  · by_cases htc : t = σ.curThread
    · exact Or.inl (act_cn_nr (a1 htc))
    rcases hcr with h | h | h
    · exact Or.inl (by rw [b1 htc]; exact h)
    · refine Or.inr (Or.inl fun x' hx' => ?_)
      rw [ct] at hx'
      by_cases e : σ.curThread = i
      · rw [e, ki] at hx'; cases hx'
      rw [ko _ (fun e' => htc e'.symm) e] at hx'
      exact h x' hx'
    · exact Or.inr (Or.inr (by rw [ct, hidl]; exact h))

end

end Fl4Proofs.P3.Sched

-- ===== from ScJointFrame
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
noncomputable section
section Spec
open Fl4Spec
end Spec
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
set_option maxHeartbeats 1000000 in
/-- **`JAtZR` across an SC step** (module docstring). -/
theorem JAtZR.sc_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hX : XTopAt (L := L) AR Z s' a' σ')
    (hcall : Sched.CallRel (L.mem s') Z.R Z.C σ' Lst') (hrf : Sched.RFree (L.mem s') Z.R Z.C σ' Lst')
    (hyl : Sched.YieldRel Z.T Z.C (L.mem s') σ') (hmcp : Sched.McpRel Z.T (L.mem s') σ')
    (hbuf : BufWordRel Z.T (L.mem s') σ')
    (hrp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ') (hap : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ')
    (hjpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ') (hjc : Sched.JCovD (L := L) Z.th H Z.G D' Cs s')
    (hkern : JKern (L := L) H Cs D' Z.th s' σ')
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi)
    (hnsc : Sched.NSC Z.N Z.C σ') (hinv : Sched.Inv σ') (hcur : CurInvR σ')
    (hown : Sched.CurOwnW Z.T Z.C σ') (hoff : Sched.OffOK σ')
    (hact : Sched.ActIdle σ') (hbsa : Sched.BlockedScActive σ') (hcr : CurRunM σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hidl : L.idleW s' = L.idleW s) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    JAtZR (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl' : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (J.obj.tkw hK) hblk J.hset.2.1 hjpl J.c0
  have hsv : Sched.SchedValid σ' := schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (J.obj.tkw hK) hblk J.hset.1
    J.hset.2.1 hcall hyl J.c0 hinv hsl
  refine ⟨hX, hcall, hrf,
    J.rrecv.frame (Sched.TFoot.keep J.xtop.fin.1.1.1 J.rp hw).2.2 (Sched.KhRB.of_sctkw hK), hyl, hmcp, hbuf,
    by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, hrp, hap,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, hjpl, J.cover.tkw hK, J.obj.tkw hK, J.zH, ?_, J.hset, J.hscC, hjc, hkern,
    J.del.of_same hSS, UtInv.of_same hM J.ut hSS, J.bound, fun G hG => ?_, hutc, hnsc, hinv, hcur, hown, hoff, hact,
    J.c0, hbsa, hsv, J.isorted.tkw hK, hsl, hcr, hblk, by rw [hks]; exact J.intL,
    J.vsc.of_eq fun y hy => hSS.capV hy,
    J.bok.keep (IpcFrKeep.of_otk hK.kh), J.fcov.ipcFr (IpcFrKeep.of_otk hK.kh),
    J.fcap.keepU (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (IpcFrKeep.of_otk hK.kh).page,
    J.ext.ss hSS (VKeep.of_tfoot J.xtop.fin.1.1.1 J.thT hw),
    J.liveX hX rfl rfl rfl hSS hKd hK.orig hidl (fun p hp => hjc.dead p (hDD p hp)), J.zDX hSS hDD⟩
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', ?_, le_rfl⟩) hK.ksz
    rw [← hSS.capV (hsl' x' hx')]; exact hc
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)


end
end
end Fl4Proofs.P3
-- ===== from ScJointRest
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
/-- **`BufWordRel` after an SC step.** -/
theorem JAtZR.sc_buf {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') :
    BufWordRel Z.T (L.mem s') σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  exact J.buf.frame (fun t ht => hw.mem_eq (tIpcBufA_aligned (hc.tcbs t ht)) fun hb => hb.ne_buf hS ht rfl)
    hK.bufKeep


/-- **`SlotsApart` after an SC step.** -/
theorem JAtZR.sc_apart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') :
    Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ' :=
  J.apart.sc_frame hw.1 hK.szKeep


/-- **`JPlaced` after an SC step.** -/
theorem JAtZR.sc_jpl {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hwU : P1.WritesIn st s s' (UFoot st Z.T Z.N Z.C Z.R Z.c s σ) := hw.mono fun b hb => Or.inl hb
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := slotsSame_of_ufoot hJ.pl hS J.rp J.apart hwU
  have hIA := hJ.irqApart (c := Z.c) J.zH.1 J.zH.2.2.2 J.c0 J.zH.2.2.1 J.kern.ksbFit
  exact ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => hK.szKeep q.bv y n hq) hw.1 (irq_of_ufoot hS J.rp hIA hwU) hiw⟩



/-- **`JKern` after an SC step**: the current thread and SC words are the
spec's, which the step keeps (`ScTKw`, `FK`); the node-0 `DEBUG_TCBS` word
kept (`hDbg`, P1-supplied); the dead set shrinking. -/
theorem JAtZR.sc_kern {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {P : Fl4Spec.ObjRef → Prop} {D' : Set U64}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') (hF : FK σ σ')
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hD : D' ⊆ D) : JKern (L := L) H Cs D' Z.th s' σ' := by
  have K := J.kern
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hX'.fin.1.1.1.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hK.ct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hF.1]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => K.orig sl (by rw [← hK.orig]; exact h), by rw [ecw, hK.ct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    ⟨pt, by rw [hK.arch]; exact hK.archObj hpt⟩, by rw [hK.arch]; exact K.ga, by rw [hK.arch]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0⟩
  rw [hna, hDbg]; exact K.head



set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after an SC step**: the caps kept (slots
apart), the free parts zero (no SC-step word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state and
the node-0 `DEBUG_TCBS` word (`hDbg`, P1-supplied). -/
theorem JAtZR.sc_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj hS h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hK.cdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [hK.arch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases tfoot_tcb hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
      omega
    · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) n.bv _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
      omega
    · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
      omega
  · intro g h0 hf0
    rw [hK.cdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← hK.orig]; exact h), by rw [hna, hDbg]; exact r3⟩


end
end
end Fl4Proofs.P3
-- ===== from ScDeadStep
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section Spec
open Fl4Spec
end Spec
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across an SC step** (module docstring), for one
dead object `q`: if `q` is a thread whose state may change (`P`), it keeps an
`Inactive` state (`deadP_sc_stepG` for every such thread). -/
theorem JAtZR.deadP_sc_stepQm {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ') {q : U64}
    (hP : ∀ x, P q.bv → σ.kheap q.bv = some (.tcb x) → tsCode x.tcbState = 0 →
      ∀ y, σ'.kheap q.bv = some (.tcb y) → y.tcbState = x.tcbState)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hYm : YMemDead (L := L) H Z.C s s' q)
    (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hS' := hX'.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have hI := hX.ipc
  have hI' := hX'.ipc
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_, fun z hq => ?_⟩
  · -- a TCB
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd.1 hq
    have hqT : q ∈ Z.T := by rw [J.tcbs_eq.1]; exact hq
    obtain ⟨x, hk, hR⟩ := hI.tcb q hqT
    obtain ⟨x', hk', hR'⟩ := hI'.tcb q hqT
    obtain ⟨y, hy, hso, hst⟩ := hK.tcb hk
    rw [hk'] at hy; cases hy
    have hst0 : tsCode x.tcbState = 0 := by
      have := hR.st; rw [← stA_tStA, d1] at this; unfold sched.TS_INACTIVE at this; simpa using this.symm
    have hstate : x'.tcbState = x.tcbState := by
      rcases hst with e | ⟨hp, -, -⟩
      · exact e
      · exact hP _ hp hk hst0 _ hk'
    have hxs : x.tcbSchedContext = none := by rw [hR.sc, d2, optRef_zero]
    have hxs' : x'.tcbSchedContext = none := by
      obtain ⟨y2, hy2, e⟩ := hL.tcb hW hk
      rw [hk'] at hy2; cases hy2
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_, ?_, ?_, hYm.1 hq d6⟩
    · have h1 : (L.mem s' (tStA q)).val = (L.mem s (tStA q)).val := by rw [hR'.st, hR.st, hstate]
      rw [stA_tStA, UScalar.eq_of_val_eq h1, ← stA_tStA, d1]
    · exact optRef_eq_none (by rw [← hR'.sc, hxs'])
    · have hb : x'.tcbBoundNotification = x.tcbBoundNotification := by rw [hso]
      have h1 := hR.bound
      rw [show tBoundA q = P1.boundA q from rfl, d3, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.boundA q = tBoundA q from rfl, ← hR'.bound, hb, h1])
    · intro e
      have hact := hS'.act
      have ea : L.actionW s' = nodeW st s' Z.c layout.node.SCHED_ACTION := by
        unfold P1.LawfulStore.actionW nodeW; rw [hc'.cur]
      rw [← ea, ← e] at hact
      revert hact
      cases hsa : σ'.schedulerAction with
      | resumeCurThread =>
        intro h; simp only [ActRel] at h; subst h
        rw [J.kern.h0] at hq; cases hq
      | chooseNewThread =>
        intro h; simp only [ActRel] at h; subst h
        have := J.kern.heap.align _ _ hq
        simp [P1.HKind.bits] at this
      | switchThread t =>
        intro h; simp only [ActRel] at h
        obtain ⟨-, -, ht⟩ := h
        obtain ⟨x2, scp, -, -, hk2, hsc2, -⟩ := schedulable_inv (hAS t hsa)
        rw [← ht, hk'] at hk2; cases hk2
        rw [hxs'] at hsc2; cases hsc2
    · have ei : L.idleW s' = L.idleW s := by
        unfold P1.LawfulStore.idleW
        apply P1.eq_of_bv
        have h1 := hs'.idleTh; have h2 := hs.idleTh
        unfold nodeW at h1 h2
        rw [hc'.cur, hc.cur, ← h1, ← h2, hF.2.1]
      rw [ei]; exact d5
  · -- an endpoint
    have hqE : q ∈ Z.E := J.hset.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ep q hqE
    obtain ⟨x', hk', hR'⟩ := hI'.ep q hqE
    rw [hK.ep hk] at hk'; cases hk'
    rw [epState_eq, stOf_ep hR hR', ← epState_eq]; exact hd.2.1 hq
  · -- a notification
    obtain ⟨d1, d2, d3⟩ := hd.2.2.1 hq
    have hqN : q ∈ Z.N := J.hset.2.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ntfn q hqN
    obtain ⟨x', hk', hR'⟩ := hI'.ntfn q hqN
    obtain ⟨y, hy, ho, hb⟩ := hK.ntfn' hk
    rw [hk'] at hy; cases hy
    have hxs : x.ntfnSc = none := by rw [hR.sc, show nScA q = P1.ntfnScA q from rfl, d3, optRef_zero]
    have hxs' : x'.ntfnSc = none := by
      obtain ⟨y2, hy2, e⟩ := hL.ntfn hW hk
      rw [hk'] at hy2; cases hy2
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_⟩
    · rw [epState_eq]
      have hO' := hR'.obj
      rw [ho] at hO'
      rw [stOf_ntfn hR.obj hO', ← epState_eq]; exact d1
    · have h1 := hR.bound
      rw [show nBoundA q = P1.ntfnBtA q from rfl, d2, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.ntfnBtA q = nBoundA q from rfl, ← hR'.bound, hb, h1])
    · exact optRef_eq_none (by rw [show P1.ntfnScA q = nScA q from rfl, ← hR'.sc, hxs'])
  · -- a reply
    have hqR : q ∈ Z.R := J.hset.2.2 q hq
    obtain ⟨x, hk, hR⟩ := hI.reply q hqR
    obtain ⟨x', hk', hR'⟩ := hI'.reply q hqR
    obtain ⟨y, hy, e⟩ := hK.reply hk
    rw [hk'] at hy; cases hy
    have h1 := hR
    rw [show Endp.rTcbA q = P1.rTcbA q from rfl, hd.2.2.2.1 hq, optRef_zero] at h1
    exact optRef_eq_none (by rw [show P1.rTcbA q = Endp.rTcbA q from rfl, ← hR', e, h1])
  · -- an SC
    obtain ⟨d1, d2, d3, d4⟩ := hd.2.2.2.2 z hq
    by_cases hqC : q ∈ Z.C
    · obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
      obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
      obtain ⟨y, hy, e1, e2⟩ := hL.sc hW hk
      rw [hk'] at hy; cases hy
      have hxt : x.scTcb = none := by rw [hR.tcb, scW_tcb, d1, optRef_zero]
      have hxn : x.scNtfn = none := by rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb]; refine optRef_eq_none ?_; rw [← hR'.tcb]
        rcases e1 with e | e
        · rw [e, hxt]
        · exact e
      · rw [(TFoot.keep hS J.rp hw).2.1 q hqC]; exact d2
      · rw [← scW_ntfn]; refine optRef_eq_none ?_; rw [← hR'.ntfn]
        rcases e2 with e | e
        · rw [e, hxn]
        · exact e
      · exact hYm.2 z hq hqC d4
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb, J.sc_out_keep hw hq hqC (by decide) (by decide), scW_tcb]; exact d1
      · rw [scReplyA_eq', J.sc_out_keep hw hq hqC (by decide) (by decide), ← scReplyA_eq']; exact d2
      · rw [← scW_ntfn, J.sc_out_keep hw hq hqC (by decide) (by decide), scW_ntfn]; exact d3
      · rw [scYieldFromA_eq, J.sc_out_keep hw hq hqC (by decide) (by decide), ← scYieldFromA_eq]; exact d4


/-- **The dead stay dead across an SC step** (`deadP_sc_stepQm` with the
yield words read through the spec, `ymd`). -/
theorem JAtZR.deadP_sc_stepQ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ') {q : U64}
    (hP : ∀ x, P q.bv → σ.kheap q.bv = some (.tcb x) → tsCode x.tcbState = 0 →
      ∀ y, σ'.kheap q.bv = some (.tcb y) → y.tcbState = x.tcbState)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') (hYD : YDeadKeep σ σ' q.bv)
    (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_sc_stepQm hX' hw hK hP hL hF hAS (J.ymd hX'.fin.1.1.1 hY' hYD) hW hd


set_option maxHeartbeats 400000 in
/-- **The dead stay dead across an SC step** (module docstring); a thread
whose state may change (`P`) keeps an `Inactive` state. -/
theorem JAtZR.deadP_sc_stepG {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ')
    (hP : ∀ p x, P p → σ.kheap p = some (.tcb x) → tsCode x.tcbState = 0 →
      ∀ y, σ'.kheap p = some (.tcb y) → y.tcbState = x.tcbState)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') {q : U64} (hYD : YDeadKeep σ σ' q.bv)
    (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_sc_stepQ hX' hw hK (fun x => hP _ x) hL hF hAS hY' hYD hW hd


/-- **The dead stay dead across an SC step** (module docstring;
`deadP_sc_stepG` with the changed threads runnable). -/
theorem JAtZR.deadP_sc_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ')
    (hP : ∀ p x, P p → σ.kheap p = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') {q : U64} (hYD : YDeadKeep σ σ' q.bv)
    (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_sc_stepG hX' hw hK (fun p x hp hk h0 => absurd h0 (tsCode_ne_of_runnable (hP p x hp hk))) hL hF hAS hY'
    hYD hW hd


end
end
end Fl4Proofs.P3
-- ===== from XTopJointFinW
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
end
end
end Fl4Proofs.P3
-- ===== from XTopJointFinThreadSc
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical
noncomputable section
end
end Fl4Proofs.P3.Sched
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
/-- **The action and idle words at `JAtZR` against the spec's**: a TCB `t`
neither word is not the spec's switch target nor its idle thread. -/
theorem JAtZR.spec_of_words (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64}
    (hna : L.actionW s ≠ t) (hid : L.idleW s ≠ t) :
    (∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) ∧ t.bv ≠ σ.idleThread := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have ea : L.actionW s = nodeW st s Z.c layout.node.SCHED_ACTION := by
    unfold P1.LawfulStore.actionW nodeW; rw [hc.cur]
  have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
    unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]
  refine ⟨fun u hu e => ?_, fun e => ?_⟩
  · have h := hS.act
    rw [hu] at h
    obtain ⟨-, -, hw⟩ := h
    apply hna; rw [ea]; apply P1.eq_of_bv
    rw [hw, e]
  · apply hid; rw [ei]; apply P1.eq_of_bv; rw [← hs.idleTh, ← e]


/-- The converse of `JAtZR.spec_of_words` for a TCB of the set. -/
theorem JAtZR.words_of_spec (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    L.actionW s ≠ t ∧ L.idleW s ≠ t := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have ea : L.actionW s = nodeW st s Z.c layout.node.SCHED_ACTION := by
    unfold P1.LawfulStore.actionW nodeW; rw [hc.cur]
  have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
    unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]
  have ta := hc.tcbs t ht
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h := hS.act
    rw [← ea, e] at h
    cases ha : σ.schedulerAction with
    | resumeCurThread =>
      rw [ha] at h
      have h0 : t = 0#u64 := h
      exact ta.ne0 (by rw [h0]; rfl)
    | chooseNewThread =>
      rw [ha] at h
      have h1 : t = 1#u64 := h
      have hv : t.val = 1 := by rw [h1]; rfl
      have := ta.align
      rw [hv] at this; norm_num at this
    | switchThread u =>
      rw [ha] at h
      exact hsa u ha h.2.2.symm
  · apply hid; rw [hs.idleTh, ← ei, e]


end
end
end Fl4Proofs.P3
-- ===== from XTopJointRecvSigRet
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical
noncomputable section
end
section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
end
end Fl4Proofs.P3.Sched
namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched
noncomputable section
section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
end
end
end Fl4Proofs.P3.Ipc
namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts
section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
end
end Fl4Proofs.P1
namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
noncomputable section
section Spec
open Fl4Spec Classical
end Spec
end
end Fl4Proofs.P3.Sched
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
set_option maxHeartbeats 8000000 in
/-- **`maybe_return_sched_context` at `J`** (module docstring), for a thread
`t` in no queue (spec `hnq`, FL4 `hout`: not runnable, or the running current
thread of a receive, XTopJointRecvIpcRet), neither the idle thread nor the
switch target, whose SC `i` is the notification `n`'s. -/
theorem JAtZR.maybeReturnJQ (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {t n i : U64} {x : Fl4Spec.Tcb}
    {xn : Fl4Spec.Notification} (ht : t ∈ Z.T) (hn : n ∈ Z.N) (hiC : i ∈ Z.C)
    (hk : σ.kheap t.bv = some (.tcb x)) (hkn : σ.kheap n.bv = some (.notification xn))
    (hsp : x.tcbSchedContext = some i.bv) (hxn : xn.ntfnSc = some i.bv) (hnq : NotQueued σ t.bv)
    (hout : (L.mem s (P1.inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    notification.maybe_return_sched_context st s n t ⦃ s' =>
      P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ) ∧ ∃ σ',
      Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZR (L := L) arI AR Z H Cs Ac' Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨y, m, hky, hyt⟩ := J.inv.back t.bv x i.bv hk hsp
  obtain ⟨σ2, he, kt, ki, ko, -⟩ := maybeReturn_shape J.inv hkn hk hky hsp hxn hnq
  have hm : ((), σ2) ∈ (Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ).1 := by
    rw [he]; exact Set.mem_singleton _
  obtain ⟨-, hidle⟩ := J.words_of_spec ht hsa hid
  have htP : t ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact ht
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  refine WP.spec_mono (WP.spec_and (WP.spec_and (maybe_return_refines s σ hR hS J.inv.actReady t n ht hn)
    (maybe_return_sfoot hS ht hiC hk hsp))
    (WP.spec_and (P1.notification.maybe_return_sched_context.inv s n t Q0 R0 h0 hB0 hX0 hS0 hSg0 htP hout hidle)
      (P1.notification.maybe_return_sched_context.kw s n t Q0 R0 h0 hB0 hX0 hS0 hSg0 htP hout hidle))) ?_
  rintro s' ⟨⟨⟨-, σ0, hm0, hf, hv, hS'⟩, hw5⟩, hP1, hfoot⟩
  rw [he] at hm0
  have e0 : σ0 = σ2 := congrArg Prod.snd (Set.mem_singleton_iff.1 hm0)
  rw [e0] at hS' hv
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' :=
    ⟨hP1.1, hP1.2.1, hP1.2.2.1, hP1.2.2.2.1, hP1.2.2.2.2.1⟩
  have hR' : NtfnStateRel Z.N Z.T (L.mem s') σ2 := hR.frame hS.placed hf hv
  have hN' : NSC Z.N Z.C σ2 := fun q hq x' p hx hp => J.nsc q hq x' p (by
    by_cases e1 : q.bv = t.bv
    · rw [e1, kt] at hx; cases hx
    by_cases e3 : q.bv = i.bv
    · rw [e3, ki] at hx; cases hx
    rw [ko _ e1 e3] at hx; exact hx) hp
  have hI' : Inv σ2 := Inv.retQ J.inv hk hkn hnq hm
  have hWk : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) :=
    Sched.WritesIn.kfoot_of_sfoot_scw hS hiC (K := 24#u64) (by simp) (by simp) (by decide) hw5
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := Sched.WritesIn.tfoot_of_kfoot hWk
  have hK : ScTKw (fun _ => False) σ σ2 := nkt_maybeReturnSc n.bv t.bv σ ((), σ2) hm
  have hX' : XTopAt (L := L) AR Z s' a σ2 :=
    xtop_sc_step (ct := σ.curThread) hX J.ip J.nk hW (hK.mono fun _ h => h.elim) hS' hR' id
  have hall := ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree
    ⟨⟨hS', hR', hN', hI'⟩, hWk, (pres_maybeReturnSc (true, true) _ _).of_eq he⟩
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  obtain ⟨hcur', hown', hoff', hact', hcr', hF⟩ := maybeReturn_midR (T := Z.T) J.inv hky hyt hk hsp hkn hxn hnq
    ⟨i, hiC, rfl⟩ hsa hid J.cur J.own J.off J.act J.curRun he
  have hB' : BlockedScActive σ2 :=
    J.bsa.bk (bk_of_tk_sk hK (skm_maybeReturnSc _ _ σ _ hm)) ((pres_maybeReturnSc (true, true) _ _).of_eq he)
  have hL : LK (fun _ => False) σ σ2 := lkm_maybeReturnSc (W := fun _ => False) n.bv t.bv σ _ hm
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) hL hF hact'.1 hY'
      ((((pres_maybeReturnSc (true, true) _ _).of_eq he).ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  exact ⟨hW, σ2, he, Ac, Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2)
    (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2))
    (J.sc_kern hW hK hF hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hN' hI' hcur' hown' hoff' hact' hB' hcr' hblk hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩


end
end
end Fl4Proofs.P3
