/-
P3 (DESIGN.md §9), scheduler: **`JAtZ` across a scheduler step**
(`JAtZ.sch_frame`, the entry tail's frame, stage 3c): `sc_frame` for the
spec's `SchStep` (the current thread and the current CR3 may change):
the heap-reading fields from `SchStep.toTK` (the step to `σ'` with `σ`'s
current thread and arch state has `σ'`'s heap).
-/
import Fl4Proofs.P3.ScJointFrame
import Fl4Proofs.P3.ScXSched
import Fl4Proofs.P3.ScJointRest
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` across a scheduler step** (module docstring). -/
theorem JAtZ.sch_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hX : XTopAt (L := L) AR Z s' a' σ')
    (hcall : Sched.CallRel (L.mem s') Z.R Z.C σ' Lst') (hrf : Sched.RFree (L.mem s') Z.R Z.C σ' Lst')
    (hyl : Sched.YieldRel Z.T Z.C (L.mem s') σ') (hmcp : Sched.McpRel Z.T (L.mem s') σ')
    (hbuf : BufWordRel Z.T (L.mem s') σ')
    (hrp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ') (hap : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ')
    (hjpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ') (hjc : Sched.JCovD (L := L) Z.th H Z.G D' Cs s')
    (hkern : JKern (L := L) H Cs D' Z.th s' σ')
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi)
    (hnsc : Sched.NSC Z.N Z.C σ') (hinv : Sched.Inv σ') (hcur : σ'.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ')
    (hown : Sched.CurOwnW Z.T Z.C σ') (hoff : Sched.OffOK σ')
    (hact : Sched.ActIdle σ') (hbsa : Sched.BlockedScActive σ') (hcr : CurRunM σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hidl : L.idleW s' = L.idleW s) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have hT := hK.toTK
  have hobj0 := J.obj.tkw hT
  have hobj : Sched.ObjCover Z.N Z.T Z.E Z.R Z.C σ' :=
    ⟨hobj0.tcb, hobj0.ntfn, hobj0.ep, hobj0.reply, hobj0.sc⟩
  have hcov0 := J.cover.tkw hT
  have hcov : Sched.SpecCover H σ' := ⟨hcov0.ntfn, hcov0.ep, hcov0.reply, hcov0.sc0, hcov0.arch⟩
  have hsrt0 := J.isorted.tkw hT
  have hsrt : Sched.IpcSorted σ' := hsrt0
  have hksz0 := hT.ksz
  have hksz : KSz σ σ' := hksz0
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl' : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (hobj) hblk J.hset.2.1 hjpl J.c0
  have hsv : Sched.SchedValid σ' := schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (hobj) hblk J.hset.1
    J.hset.2.1 hcall hyl J.c0 hinv hsl
  refine ⟨hX, hcall, hrf,
    J.rrecv.frame (Sched.TFoot.keep J.xtop.fin.1.1.1 J.rp hw).2.2 (Sched.KhRB.of_otk hK.kh), hyl, hmcp, hbuf,
    by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, hrp, hap,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, hjpl, hcov, hobj, J.zH, ?_, J.hset, J.hscC, hjc, hkern,
    J.del.of_same hSS, UtInv.of_same hM J.ut hSS, J.bound, fun G hG => ?_, hutc, hnsc, hinv, hcur, hown, hoff, hact,
    J.c0, hbsa, hsv, hsrt, hsl, hcr, hblk, by rw [hks]; exact J.intL,
    J.vsc.of_eq fun y hy => hSS.capV hy,
    J.bok.keep (IpcFrKeep.of_otk hK.kh), J.fcov.ipcFr (IpcFrKeep.of_otk hK.kh),
    J.fcap.keepU (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (IpcFrKeep.of_otk hK.kh).page,
    J.ext.ss hSS (VKeep.of_tfoot J.xtop.fin.1.1.1 J.thT hw),
    J.liveX hX rfl rfl rfl hSS hKd hK.orig hidl (fun p hp => hjc.dead p (hDD p hp)), J.zDX hSS hDD⟩
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', ?_, le_rfl⟩) hksz
    rw [← hSS.capV (hsl' x' hx')]; exact hc
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)



/-! ## The re-established fields across a scheduler step -/

/-- **`BufWordRel` after a scheduler step** (`sc_buf` through `toTK`). -/
theorem JAtZ.sch_buf {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ') :
    BufWordRel Z.T (L.mem s') σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hb0 := hK.toTK.bufKeep
  have hb : BufKeep σ σ' := hb0
  exact J.buf.frame (fun t ht => hw.mem_eq (tIpcBufA_aligned (hc.tcbs t ht)) fun hb => hb.ne_buf hS ht rfl) hb

/-- **`SlotsApart` after a scheduler step.** -/
theorem JAtZ.sch_apart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ') :
    Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ' := by
  have hz0 := hK.toTK.szKeep
  have hz : Sched.SzKeep σ σ' := hz0
  exact J.apart.sc_frame hw.1 hz

/-- **`JPlaced` after a scheduler step.** -/
theorem JAtZ.sch_jpl {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hz0 := hK.toTK.szKeep
  have hz : Sched.SzKeep σ σ' := hz0
  have hwU : P1.WritesIn st s s' (UFoot st Z.T Z.N Z.C Z.R Z.c s σ) := hw.mono fun b hb => Or.inl hb
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := slotsSame_of_ufoot hJ.pl hS J.rp J.apart hwU
  have hIA := hJ.irqApart (c := Z.c) J.zH.1 J.zH.2.2.2 J.c0 J.zH.2.2.1 J.kern.ksbFit
  exact ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => hz q.bv y n hq) hw.1 (irq_of_ufoot hS J.rp hIA hwU) hiw⟩


set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after a scheduler step** (`sc_utc`'s proof; the
global PML4 kept by `SchStep`): the caps kept (slots
apart), the free parts zero (no SC-step word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state and
the node-0 `DEBUG_TCBS` word (`hDbg`, P1-supplied). -/
theorem JAtZ.sch_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
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
    fun g => by rw [hK.gpml4]; exact U.gReg (B g)⟩
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
