/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr7): **the TCB cap installs
at `MachPlat`**: XTopJointTcbInstall's `install_tcb_capJ` … `tcb_configureJ`
and XTopJointTcbSsp's `install_fhJ` … `tcb_set_sched_paramsJ` with the
deletion loop's preempted invariant `WJPM` (XTopJointMRDel: `WJP` and
`JAtPreMV`) for `WJP`, so a preempted install ends in `JAtPreMV` (what mr4's
`decOK_JM` asks of the `JPreDecHyp` kinds). Generated: scratch/mr7/gentcb.py
+ headT.lean. The copies (names with an `M` suffix: `TcbInsWM`,
`install_tcb_capJM`, …, `tcb_set_sched_paramsJM`) differ from the originals
only in the preempted invariant (`TcbInsWM.del : DelHypsWRZ (W kb) (WJPM ..)`)
and in `top_of_instJM`'s / `ssp_tailJM`'s preempted branch, which reads
`JAtPreMV` off `WJPM`.
-/
import Fl4Proofs.P3.XTopJointTcbSsp
import Fl4Proofs.P3.XTopJointMRDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- **`tcb::install_tcb_cap` at `J`** (module docstring): from the
deletion loop's invariant `WJR` at the base sets `Z`, `WJR` after an Ok
install, `WJP` after a preempted one. -/
theorem install_tcb_capJM [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJPM (L := L) arI AR MR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (hn2 : n ≠ 2) (idx : U64) (hidx : idx.val = n)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (nc : capability.Cap) (hwf : CapWf nc) (hcv : CapValid Z.th nc) (he : EncWf nc)
    (hfw : isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {srcC0 : capability.Cap} (hsrc0 : capV (L.mem s0) (cslotAddr (ps.bv, idxs)) = srcC0)
    (hsh : shape nc = shape srcC0) (hbd : badgeF nc = badgeF srcC0 ∨ badgeF srcC0 = 0#u64)
    (hkey : okey nc = okey srcC0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC0 → Vs.VCapOK P L4 L3 L2 L1 nc)
    (htu : Vs.TabUn nc → Vs.TabUn srcC0) (hnat : Vs.NativeCap srcC0 → Vs.NativeCap nc)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr (ps.bv, idxs)) ⦃ res =>
      InstPostWP (L := L) W (WJPM (L := L) arI AR MR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, (ps.bv, idxs)))) s0 σ res ⦄ := by
  obtain ⟨V0, Ac0, Lst0, D0, J0, -, -, -⟩ := hI.wjr _ _ _ _ hW
  have hP : Placed Z.th := J0.xtop.rel.1
  obtain ⟨K, hK, hK6, hDE⟩ := J0.delE
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot Z.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsrcT := cnode_slot_ne_tcb hP hps hls ht
  have hczs0 := hcz0.1 _ hAsrc.isSlot hsrcT
  have hsh0 : shape nc = shape (capV (L.mem s0) (cslotAddr (ps.bv, idxs))) := by rw [hsrc0]; exact hsh
  -- the insert after the delete, at `WJR`
  have after : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost), DState (L := L) Z.th s1 σ1 G1 →
      W s1 a1 σ1 G1 →
      capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null →
      ChgZ (L.mem s0) (L.mem s1) (cslotAddr (ps.bv, idxs)) →
      (do
        let b ← nc.is_null
        if b = true then ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)
          else do
            let b1 ← tcb.still_valid st s1 t (cslotAddr ssl) nc (cslotAddr (ps.bv, idxs))
            if b1 = true then do
                let s2 ← cdt.insert st s1 nc (cslotAddr (ps.bv, idxs)) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))
                ok (core.result.Result.Ok (), s2, a1)
              else ok (core.result.Result.Ok (), s1, a1)) ⦃ res =>
        ∃ σ' G', (Fl4Spec.NonDetE.unlessE (ε := Unit) (absCap nc = .nullCap) (Fl4Spec.NonDetE.liftE
            (Fl4Spec.checkCapAt (absCap nc) (ps.bv, idxs) (Fl4Spec.checkCapAt (.threadCap t.bv) ssl
              (Fl4Spec.capInsert (absCap nc) (ps.bv, idxs) (t.bv, Fl4Spec.tcbCnodeIndex n)))))).run σ1 =
              ({(.ok (), σ')}, False) ∧
          res.1 = .Ok () ∧ DState (L := L) Z.th res.2.1 σ' G' ∧
          (∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
            capV (L.mem res.2.1) y = capV (L.mem s1) y) ∧
          (capV (L.mem res.2.1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null ∨
            capV (L.mem res.2.1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = nc) ∧
          W res.2.1 res.2.2 σ' G' ⦄ := by
    intro s1 a1 σ1 G1 hDS1 hW1 hroot hczs
    refine WP.spec_mono (WP.spec_and (install_after Z.th hP s0 s1 a1 σ1 G1 hDS1 t ht n hn hroot ssl hAs nc hwf hcv he
      hfw hps hls hczs hsrc0 hsh hbd hkey hv)
      (install_after_frame hP s1 a1 hDS1.1.2.2.1 hDS1.2.1 t (cslotAddr ssl) nc hAsrc.isSlot hAt.isSlot)) ?_
    rintro res ⟨⟨σ', G', hrun, hr1, ha1, hDS', hcap, hst, htg, hcase⟩, hF⟩
    refine ⟨σ', G', hrun, hr1, hDS', hcap, htg, ?_⟩
    rcases hcase with ⟨e1, e2, e3⟩ | ⟨hins, hthr, hsrc1, hnn, hnut, hdst⟩
    · rw [ha1, e1, e2, e3]; exact hW1
    obtain ⟨V1, Ac1, Lst1, D1, J1, hkb1, hns1, hsg1, hp1⟩ := hI.wjr _ _ _ _ hW1
    have hsg' : SpecGlob σ' := by
      obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS1.1.1.abs_cap hAsrc
      have e0 : c0 = srcC0 := by rw [← hsrc1, capV_of_capAt hc0]
      have ha0 := (getCap_set_iff σ1 _ _ _).1 (congrArg Prod.fst hg0)
      rw [hca0.abs, e0] at ha0
      exact hsg1.insTcb hins hnut hsh ha0
    have hwS := SlotFrame2.writesIn hF
    obtain ⟨Ac2, Lst2, D2, J2⟩ := J1.insTJ (fun e => absurd e hn2) ht hn hins hDS' hst hwS hroot hcap
      (by rw [hdst]; exact hnut) (by rw [hdst]; exact hnn) ⟨_, hAsrc.isSlot, by rw [hdst, hsrc1]; exact hsh⟩
      (fun h3 => by rw [hdst]; exact Or.inr (hep h3 hnn)) (fun e => absurd e hn2) ⟨_, hAs.isSlot, hthr⟩
      (fun P L4 L3 L2 L1 h => by
        rw [hdst]; exact h.copy hAsrc.isSlot (by rw [hsrc1]; exact hv) (by rw [hsrc1]; exact htu))
      (fun U h => by rw [hdst]; exact (h _ hAsrc.isSlot).of_okey (by rw [hsrc1]; exact hkey))
      (fun h => by rw [hdst]; exact hnat (by rw [← hsrc1]; exact h _ hAsrc.isSlot))
    have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap nc) (ps.bv, idxs)
        (t.bv, Fl4Spec.tcbCnodeIndex n) σ1).1 := by rw [hins]; rfl
    have hcn := capInsert_nkn _ _ _ σ1 _ hmem
    have hact : σ'.schedulerAction = σ1.schedulerAction := by
      have e := congrArg Fl4Spec.AbstractState.schedulerAction hcn.1; exact e
    rw [ha1]
    exact hI.ins s1 res.2.1 a1 σ1 σ' G1 G' t n _ _ hDS1 hW1 hDS'
      ⟨V1, Ac2, Lst2, D2, J2, by rw [hwS.1]; exact hkb1, fun u e => hns1 u (hact ▸ e), hsg',
        hp1.of_ppk (PPK.of_cnK hcn)⟩ ht hn hins hwS hroot hcap (by rw [hdst]; exact hnn)
      ⟨_, hAsrc.isSlot, by rw [hdst, hsrc1]; exact hsh⟩ ⟨_, hAs.isSlot, hthr⟩
  unfold tcb.install_tcb_cap
  rw [spec_eq_ok (tcb_slot_spec t idx), tcb_root_eq t idx hn hidx]
  simp only [bind_ok]
  obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAt
  by_cases hc0n : c0 = .Null
  · subst hc0n
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    refine WP.spec_mono (after s a σ G hDS hW (by rw [capV_of_capAt hc0]) hczs0) ?_
    rintro res ⟨σ', G', hrun, hr1, hDS', hcap, htg, hW'⟩
    have hg0' : Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({(.nullCap, σ)}, False) := by
      rw [hg0, hca0.abs]; rfl
    exact ⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok (by rw [capDelete_null hg0']; rfl) (mem_of_run hrun),
      hcz0.install hP ht hn (fun y hy hne => ChgZ.of_eq (hcap y hy hne)) htg hAsrc.isSlot hsh0 hep, hW'⟩, hDS'⟩
  · apply WP.spec_bind (delete_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 _ hAt s a σ G hDS hW
      (by rw [capV_of_capAt hc0]; exact hc0n) (hDE.2.1 G hDS.1.2.2.1))
    rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, -, -, hmD, hcase, hW1⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD hW1 ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_mono (after s1 a1 σ1 G1 hDS1 hW1 hnull (hczs0.trans (hcz _ hAsrc.isSlot (hsrcT n hn)))) ?_
      rintro res ⟨σ', G', hrun, hr1, hDS', hcap, htg, hW'⟩
      exact ⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok hmem (mem_of_run hrun),
        hcz0.install hP ht hn (fun y hy hne => (hcz y hy hne).trans (ChgZ.of_eq (hcap y hy hne))) htg
          hAsrc.isSlot hsh0 hep, hW'⟩, hDS'⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem, hW1⟩, hDS1⟩

/-- `install_tcb_capJM` with the new cap's conditions as `NewCapOK`. -/
theorem install_okJM [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJPM (L := L) arI AR MR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (hn2 : n ≠ 2) (idx : U64) (hidx : idx.val = n)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (nc : capability.Cap) (sl : Fl4Spec.CslotPtr) (hok : NewCapOK Z.th (L.mem s0) nc sl)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr sl) ⦃ res =>
      InstPostWP (L := L) W (WJPM (L := L) arI AR MR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, sl))) s0 σ res ⦄ := by
  obtain ⟨ps, rs, hps, h1s, hls, hwf, hcv, he, hfw, hsh, hbd, hkey, hvk, htu, hnat⟩ := hok
  obtain ⟨sa, idxs⟩ := sl
  simp only at h1s hls; subst h1s
  exact install_tcb_capJM arI hI hH s0 s a σ G hDS hW t ht n hn hn2 idx hidx hcz0 ssl hAs nc hwf hcv he hfw hps hls rfl
    hsh hbd hkey hvk htu hnat hep

set_option maxHeartbeats 16000000 in
/-- **`tcb::install_buffer` at `J`** (as TcbCaps' `install_buffer_refinesW`):
the delete of the buffer slot by `delete_fullWR` (`WJP` when preempted), the
IPC buffer's word and the scheduler at `WJR` (`BufHypW`), the frame cap's
checks and insert by `check_insert`, the insert by `JAtZ.insTJ`. -/
theorem install_bufferJM [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJPM (L := L) arI AR MR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G) (t : U64) (ht : Z.th t = some .tcb)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : BufHypW (L := L) W Z.th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK Z.th (L.mem s0) c sl)
    (hbfd : ∀ c sl, bfr = some (c, sl) → BufFrOK ptr c) (hfnz : ∀ c sl, bfr = some (c, sl) → FrNZ Z.th (L.mem s0)) :
    tcb.install_buffer st arI s a t (cslotAddr ssl) addr (bufArg bc0 bfr) ⦃ res =>
      InstPostWP (L := L) W (WJPM (L := L) arI AR MR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbFrameCap t.bv ssl (some (ptr, frameOf bfr))) s0 σ res ⦄ := by
  obtain ⟨V0, Ac0, Lst0, D0, J0, -, -, -⟩ := hI.wjr _ _ _ _ hW
  have hP : Placed Z.th := J0.xtop.rel.1
  obtain ⟨K, hK, hK6, hDE⟩ := J0.delE
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
  obtain ⟨c, s3, hbuf⟩ : ∃ c s3, bufArg bc0 bfr = (c, s3) := ⟨_, _, rfl⟩
  have cont : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost), DState (L := L) Z.th s1 σ1 G1 →
      W s1 a1 σ1 G1 →
      capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) = .Null →
      InstFr Z.th t (L.mem s0) (L.mem s1) →
      (.ok (), σ1) ∈ ((Fl4Spec.capDelete (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex 2)).run σ).1 →
      (do
        let s2 ← obj.Tcb.set_ipc_buffer st t s1 addr
        let b ← tcb.still_valid st s2 t (cslotAddr ssl) c s3
        let s4 ← if b = true then cdt.insert st s2 c s3 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) else ok s2
        let t_1 ← sched.cur_thread st s4
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t_1
        if b1 = true then do
            let s5 ← sched.reschedule_required st s4
            ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1)
          else ok (core.result.Result.Ok (), s4, a1)) ⦃ res =>
        InstPostWP (L := L) W (WJPM (L := L) arI AR MR Z H Cs kb) Z.th t
          (Fl4Spec.installTcbFrameCap t.bv ssl (some (ptr, frameOf bfr))) s0 σ res ⦄ := by
    intro s1 a1 σ1 G1 hDS1 hW1 hnull hcz hmem
    apply WP.spec_bind (hBuf.ipc s1 a1 σ1 G1 hDS1 hW1 hnull)
    rintro s2 ⟨hS2, σ2, hts, hCR2, hK2, hW2⟩
    have hDS2 := hDS1.of_same hS2 hCR2 hK2
    have hnull2 : capV (L.mem s2) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) = .Null := by
      rw [hS2.capV hAt.isSlot, hnull]
    cases bfr with
    | none =>
      simp only [bufArg, Prod.mk.injEq] at hbuf
      obtain ⟨rfl, rfl⟩ := hbuf
      simp only [still_valid_zero, bind_ok, Bool.false_eq_true, ↓reduceIte]
      apply WP.spec_mono (hBuf.tail s2 a1 σ2 G1 hDS2 hW2)
      rintro res ⟨hr1, -, hS5, σ5, htail, hCR5, hK6', hW5⟩
      refine ⟨σ5, G1, Or.inl ⟨hr1, ?_, (hcz.same hS2 ht).same hS5 ht, hW5⟩, hDS2.of_same hS5 hCR5 hK6'⟩
      refine mem_bindE_ok hmem (mem_bindE_ok (mem_liftE_ok hts) (mem_bindE_ok (s' := σ2) (a := ()) ?_ htail))
      exact mem_liftE_ok (x := ((), σ2)) rfl
    | some p =>
      obtain ⟨c', sl⟩ := p
      simp only [bufArg, Prod.mk.injEq] at hbuf
      obtain ⟨rfl, rfl⟩ := hbuf
      have hok := hbfr c' sl rfl
      obtain ⟨ps, rs, hps, h1s, hls, -, -, -, -, hshc, -⟩ := hok
      have hsrcIs : IsSlot Z.th (cslotAddr sl) := by
        obtain ⟨sa, idxs⟩ := sl; simp only at h1s hls; subst h1s
        exact (show AbsSlot Z.th (ps.bv, idxs) from ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩).isSlot
      have hsrcT : NotTcbSlot t (cslotAddr sl) := by
        obtain ⟨sa, idxs⟩ := sl; simp only at h1s hls; subst h1s
        exact cnode_slot_ne_tcb hP hps hls ht
      have hczs : ChgZ (L.mem s0) (L.mem s2) (cslotAddr sl) :=
        (hcz.1 _ hsrcIs hsrcT).trans (ChgZ.of_eq (hS2.capV hsrcIs))
      rw [← Std.bind_assoc]
      apply WP.spec_bind (WP.spec_and (check_insert Z.th hP s0 s2 σ2 G1 hDS2 t ht 2 (by decide) hnull2 ssl hAs c' sl
        (hbfr c' sl rfl) hczs) (check_insert_frame hP s2 hDS2.1.2.2.1 hDS2.2.1 t (cslotAddr ssl) c' hsrcIs hAt.isSlot))
      rintro s4 ⟨⟨σ4, G4, hchk, hDS4, hcap4, hst4, htg4, hcase⟩, hF4⟩
      have hW4 : W s4 a1 σ4 G4 := by
        rcases hcase with ⟨e1, e2, e3⟩ | ⟨hins, hthr, hsrc1, hnn, hnut, hdst⟩
        · rw [e1, e2, e3]; exact hW2
        obtain ⟨V2, Ac2, Lst2, D2, J2, hkb2, hns2, hsg2, hp2⟩ := hI.wjr _ _ _ _ hW2
        have hsg4 : SpecGlob σ4 := by
          obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS2.1.1.abs_cap
            (show AbsSlot Z.th sl by
              obtain ⟨sa, idxs⟩ := sl; simp only at h1s hls; subst h1s
              exact ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩)
          have e0 : c0 = capV (L.mem s0) (cslotAddr sl) := by rw [← hsrc1, capV_of_capAt hc0]
          have ha0 := (getCap_set_iff σ2 _ _ _).1 (congrArg Prod.fst hg0)
          rw [hca0.abs, e0] at ha0
          exact hsg2.insTcb hins hnut hshc ha0
        have hwS := SlotFrame2.writesIn hF4
        obtain ⟨⟨q, sz, rr, m, aa, va, hcF⟩, hbal⟩ := hbfd c' sl rfl
        obtain ⟨-, -, -, -, -, -, hcvc, -, -, -, -, hk', -, -⟩ := hbfr c' sl rfl
        have hk2 : okey c' = okey (capV (L.mem s2) (cslotAddr sl)) := by rw [hsrc1]; exact hk'
        have hq0 : q ≠ 0#u64 := by
          obtain ⟨r0, m0, e0, a0, v0, hs0⟩ : ∃ r0 m0 e0 a0 v0,
              capV (L.mem s0) (cslotAddr sl) = .Frame q sz r0 false m0 e0 a0 v0 := by
            rw [hcF] at hk'
            generalize capV (L.mem s0) (cslotAddr sl) = c0 at hk' ⊢
            cases c0 <;> simp [okey] at hk'
            obtain ⟨rfl, rfl, rfl⟩ := hk'
            exact ⟨_, _, _, _, _, rfl⟩
          exact hfnz c' sl rfl _ hsrcIs q sz r0 m0 e0 a0 v0 hs0
        have hbuf2 : ∀ x, σ2.kheap t.bv = some (.tcb x) → x.tcbIpcBuffer.toNat % 1024 = 0 := by
          intro x hx
          obtain ⟨x0, -, he⟩ := PPS.threadSet_mem hts
          have he' : σ2 = _ := he
          rw [he'] at hx
          simp only [Function.update_self, Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx
          subst hx; exact hbal
        have hbok4 := J2.bokInstall ht hins hDS4.1.1 hcap4 hdst hcF hq0 hcvc hsrcIs hk2 hbuf2
        obtain ⟨Ac4, Lst4, D4, J4⟩ := J2.insTJ (fun _ => hbok4) ht (n := 2) (by decide) hins hDS4 hst4 hwS hnull2 hcap4
          (by rw [hdst]; exact hnut) (by rw [hdst, hcF]; exact fun h => by cases h) ⟨_, hsrcIs, by rw [hdst, hsrc1]; exact hshc⟩
          (fun h => absurd h (by decide)) (fun _ => by rw [hdst, hcF]; exact Or.inr ⟨q, sz, rr, m, false, aa, va, rfl⟩)
          ⟨_, hAs.isSlot, hthr⟩
          (fun P L4 L3 L2 L1 h => by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hvk', htu', -⟩ := hbfr c' sl rfl
            rw [hdst]; exact h.copy hsrcIs (by rw [hsrc1]; exact hvk') (by rw [hsrc1]; exact htu'))
          (fun U h => by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk', -, -⟩ := hbfr c' sl rfl
            rw [hdst]; exact (h _ hsrcIs).of_okey (by rw [hsrc1]; exact hk'))
          (fun h => by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt'⟩ := hbfr c' sl rfl
            rw [hdst]; exact hnt' (by rw [← hsrc1]; exact h _ hsrcIs))
        have hmem' : ((), σ4) ∈ (Fl4Spec.capInsert (Z := Unit) (absCap c') sl
            (t.bv, Fl4Spec.tcbCnodeIndex 2) σ2).1 := by rw [hins]; rfl
        have hcn := capInsert_nkn _ _ _ σ2 _ hmem'
        have hact : σ4.schedulerAction = σ2.schedulerAction := by
          have e := congrArg Fl4Spec.AbstractState.schedulerAction hcn.1; exact e
        exact hI.ins s2 s4 a1 σ2 σ4 G1 G4 t 2 _ _ hDS2 hW2 hDS4
          ⟨V2, Ac4, Lst4, D4, J4, by rw [hwS.1]; exact hkb2, fun u e => hns2 u (hact ▸ e), hsg4,
            hp2.of_ppk (PPK.of_cnK hcn)⟩ ht (by decide) hins hwS hnull2 hcap4 (by rw [hdst]; exact hnn)
          ⟨_, hsrcIs, by rw [hdst, hsrc1]; exact hshc⟩ ⟨_, hAs.isSlot, hthr⟩
      apply WP.spec_mono (hBuf.tail s4 a1 σ4 G4 hDS4 hW4)
      rintro res ⟨hr1, -, hS5, σ5, htail, hCR5, hK6', hW5⟩
      have hAt2 : IsSlot Z.th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) := hAt.isSlot
      refine ⟨σ5, G4, Or.inl ⟨hr1, ?_, (hcz.same hS2 ht).install hP ht (n := 2) (by decide)
        (fun y hy hne => (ChgZ.of_eq (hcap4 y hy hne)).trans (ChgZ.of_eq (hS5.capV hy)))
        (by rw [hS5.capV hAt2]; exact htg4) hsrcIs hshc (fun h => absurd h (by decide)), hW5⟩,
        hDS4.of_same hS5 hCR5 hK6'⟩
      refine mem_bindE_ok hmem (mem_bindE_ok (mem_liftE_ok hts) (mem_bindE_ok (s' := σ4) (a := ()) ?_ htail))
      exact mem_liftE_ok (x := ((), σ4)) (by simp only [frameOf]; rw [hchk]; rfl)
  rw [hbuf]
  unfold tcb.install_buffer
  rw [tcb_slot_buffer]
  simp only [bind_ok]
  obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAt
  by_cases hc0n : c0 = .Null
  · subst hc0n
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    have hg0' : Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex 2) σ = ({(.nullCap, σ)}, False) := by
      rw [hg0, hca0.abs]; rfl
    exact cont s a σ G hDS hW (by rw [capV_of_capAt hc0]) hcz0 (by rw [capDelete_null hg0']; rfl)
  · apply WP.spec_bind (delete_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 _ hAt s a σ G hDS hW
      (by rw [capV_of_capAt hc0]; exact hc0n) (hDE.2.1 G hDS.1.2.2.1))
    rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, -, -, hmD, hcase, hW1⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD hW1 ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact cont s1 a1 σ1 G1 hDS1 hW1 hnull (hcz0.delete hP ht (n := 2) (by decide) hcz hnull) hmem
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem, hW1⟩, hDS1⟩

set_option maxHeartbeats 16000000 in
/-- **ThreadControl's cap installs at `J`**, as TcbCaps'
`thread_control_caps_refinesW` with `install_okJM` and `install_bufferJM`: `WJR` after an Ok run,
`WJP` after a preempted one. -/
theorem thread_control_capsJM [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJPM (L := L) arI AR MR Z H Cs kb) Rd Rz Z.th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl) (flags : U64)
    (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (hfh : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → NewCapOK Z.th (L.mem s) fh.1 fh.2)
    (htmh : (flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64 → NewCapOK Z.th (L.mem s) tmh.1 tmh.2)
    (hcr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK Z.th (L.mem s) cr.1 cr.2)
    (hvr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK Z.th (L.mem s) vr.1 vr.2)
    (hfhE : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → fh.1 ≠ .Null →
      ∃ e b x1 x2 x3 x4, fh.1 = .Endpoint e b x1 x2 x3 x4)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 → BufHypW (L := L) W Z.th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK Z.th (L.mem s) c sl)
    (hbfd : ∀ c sl, bfr = some (c, sl) → BufFrOK ptr c) (hfnz : ∀ c sl, bfr = some (c, sl) → FrNZ Z.th (L.mem s)) :
    tcb.thread_control_caps st arI s a t (cslotAddr ssl) (fh.1, cslotAddr fh.2) (tmh.1, cslotAddr tmh.2)
      (cr.1, cslotAddr cr.2) (vr.1, cslotAddr vr.2) addr (bufArg bc0 bfr) flags ⦃ res =>
      InstPostWP (L := L) W (WJPM (L := L) arI AR MR Z H Cs kb) Z.th t
        (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s σ res ⦄ := by
  have r0 : InstFr Z.th t (L.mem s) (L.mem s) := InstFr.refl _ _ _
  have i3 : (layout.tcb.SLOT_FAULT_HANDLER).val = 3 := by simp [layout.tcb.SLOT_FAULT_HANDLER]
  have i4 : (layout.tcb.SLOT_TIMEOUT_HANDLER).val = 4 := by simp [layout.tcb.SLOT_TIMEOUT_HANDLER]
  have i0 : (layout.tcb.SLOT_CTABLE).val = 0 := by simp [layout.tcb.SLOT_CTABLE]
  have i1 : (layout.tcb.SLOT_VTABLE).val = 1 := by simp [layout.tcb.SLOT_VTABLE]
  unfold tcb.thread_control_caps tcCapsSpec
  by_cases hF : (flags &&& tcb.UPDATE_FAULT) = 0#u64 <;>
  by_cases hT : (flags &&& tcb.UPDATE_TIMEOUT) = 0#u64 <;>
  by_cases hS : (flags &&& tcb.UPDATE_SPACE) = 0#u64 <;>
  by_cases hU : (flags &&& tcb.UPDATE_IPC_BUFFER) = 0#u64 <;>
  simp only [lift, bind_ok, hF, hT, hS, hU, bne_iff_ne, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte,
    optArg, installTcbCap_none, installTcbFrameCap_none] <;>
  -- the fault handler
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_okJM arI hI hH s s a σ G hDS hW t ht 3 (by decide) (by decide) _ i3 r0 ssl hAs
        _ _ (hfh hF) (fun _ => hfhE hF)) (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the timeout handler
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_okJM arI hI hH s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hW) t ht 4
        (by decide) (by decide) _ i4 (by first | assumption | exact r0) ssl hAs _ _ (htmh hT) (fun h => absurd h (by decide)))
        (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the CSpace root
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_okJM arI hI hH s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hW) t ht 0
        (by decide) (by decide) _ i0 (by first | assumption | exact r0) ssl hAs _ _ (hcr hS) (fun h => absurd h (by decide)))
        (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the VSpace root
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_okJM arI hI hH s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hW) t ht 1
        (by decide) (by decide) _ i1 (by first | assumption | exact r0) ssl hAs _ _ (hvr hS) (fun h => absurd h (by decide)))
        (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the IPC buffer
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_bufferJM arI hI hH s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hW) t ht
        (by first | assumption | exact r0) ssl hAs addr ptr (hBuf hU) bc0 bfr hbfr hbfd hfnz)
        (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  exact inst_doneWP ‹DState _ _ _ _› (by first | assumption | exact hW) (by first | assumption | exact r0)

/-- **An install run's outcome at `WJR`/`WJP` after the restart is a
`TopPostDMXP` outcome at `JAt`/`JAtPre`** of the spec's ThreadControlCaps
invocation (`XTopAt`'s `DomRel` and `MdbOKV` after an Ok run, `WJP`'s after
a preemption). -/
theorem top_of_instJM {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    (hw : ∀ s a σ G, W s a σ G → WJR (L := L) arI AR Z H Cs kb s a σ G) {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {t : U64} {ssl : Fl4Spec.CslotPtr} {flags : U64}
    {fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr} {ptr : Fl4Spec.VSpaceRef}
    {bfr : Option (capability.Cap × Fl4Spec.CslotPtr)} {s s1 : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (hdec : DecOut m σ (tcInv t ssl flags fh tmh cr vr ptr bfr))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : InstPostWP (L := L) W (WJPM (L := L) arI AR MR Z H Cs kb) Z.th t
      (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s1 σ1 res) :
    TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) σ blk call don m s res := by
  obtain ⟨σ', G', hc, hDS'⟩ := h
  rcases hc with ⟨hr, hx, -, hW'⟩ | ⟨hr, hx, hW'⟩
  · obtain ⟨V, Ac', Lst', D', J', -⟩ := hw _ _ _ _ hW'
    have hX' := J'.xtop
    refine Or.inr ⟨_, hdec, σ1, hst, tcRet (.ok (), σ'), tcCapsSpec_mem t ssl flags fh tmh cr vr ptr bfr hx,
      ⟨Z.th, G', Or.inl ⟨hr, rfl⟩, hX'.rel.1, hDS'.1, hDS'.2.2, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ?_⟩
    show if res.1 = .Err .Preempted then _ else _
    rw [if_neg (by rw [hr]; exact fun e => by cases e)]
    exact ⟨_, H, Cs, Ac', Lst', D', J'⟩
  · obtain ⟨⟨s0, a0, σ0, ⟨V, Ac', Lst', D', J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩, hPre⟩ := hW'
    refine Or.inr ⟨_, hdec, σ1, hst, tcRet (.error (), σ'), tcCapsSpec_mem t ssl flags fh tmh cr vr ptr bfr hx,
      ⟨Z.th, G', Or.inr ⟨hr, rfl⟩, J0.xtop.rel.1, hDS'.1, hDS'.2.2, hDom, hMO⟩, ?_⟩
    show if res.1 = .Err .Preempted then _ else _
    rw [if_pos hr]
    exact hPre


set_option maxHeartbeats 16000000 in
/-- **`tcb::install_tcb_cap` at `J` with the slots' frame** (`install_tcb_capJM`;
the old cap null or an endpoint cap, `NullOrEp`: an Ok install changes no
other slot's cap, by P1's `cdt.delete.ep` with `empty_capV_frame` and the
insert's frame) (module docstring): from the
deletion loop's invariant `WJR` at the base sets `Z`, `WJR` after an Ok
install, `WJP` after a preempted one. -/
theorem install_fhJM [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJPM (L := L) arI AR MR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (hn2 : n ≠ 2) (idx : U64) (hidx : idx.val = n)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (nc : capability.Cap) (hwf : CapWf nc) (hcv : CapValid Z.th nc) (he : EncWf nc)
    (hfw : isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {srcC0 : capability.Cap} (hsrc0 : capV (L.mem s0) (cslotAddr (ps.bv, idxs)) = srcC0)
    (hsh : shape nc = shape srcC0) (hbd : badgeF nc = badgeF srcC0 ∨ badgeF srcC0 = 0#u64)
    (hkey : okey nc = okey srcC0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC0 → Vs.VCapOK P L4 L3 L2 L1 nc)
    (htu : Vs.TabUn nc → Vs.TabUn srcC0) (hnat : Vs.NativeCap srcC0 → Vs.NativeCap nc)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4)
    (hnoe : P1.NullOrEp H (capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)))) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr (ps.bv, idxs)) ⦃ res =>
      InstPostWP (L := L) W (WJPM (L := L) arI AR MR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, (ps.bv, idxs)))) s0 σ res ∧
      (res.1 = .Ok () → ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
        capV (L.mem res.2.1) y = capV (L.mem s) y) ⦄ := by
  obtain ⟨V0, Ac0, Lst0, D0, J0, -, -, -⟩ := hI.wjr _ _ _ _ hW
  have hP : Placed Z.th := J0.xtop.rel.1
  obtain ⟨K, hK, hK6, hDE⟩ := J0.delE
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot Z.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsrcT := cnode_slot_ne_tcb hP hps hls ht
  have hczs0 := hcz0.1 _ hAsrc.isSlot hsrcT
  have hsh0 : shape nc = shape (capV (L.mem s0) (cslotAddr (ps.bv, idxs))) := by rw [hsrc0]; exact hsh
  -- the insert after the delete, at `WJR`
  have after : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost), DState (L := L) Z.th s1 σ1 G1 →
      W s1 a1 σ1 G1 →
      capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null →
      ChgZ (L.mem s0) (L.mem s1) (cslotAddr (ps.bv, idxs)) →
      (do
        let b ← nc.is_null
        if b = true then ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)
          else do
            let b1 ← tcb.still_valid st s1 t (cslotAddr ssl) nc (cslotAddr (ps.bv, idxs))
            if b1 = true then do
                let s2 ← cdt.insert st s1 nc (cslotAddr (ps.bv, idxs)) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))
                ok (core.result.Result.Ok (), s2, a1)
              else ok (core.result.Result.Ok (), s1, a1)) ⦃ res =>
        ∃ σ' G', (Fl4Spec.NonDetE.unlessE (ε := Unit) (absCap nc = .nullCap) (Fl4Spec.NonDetE.liftE
            (Fl4Spec.checkCapAt (absCap nc) (ps.bv, idxs) (Fl4Spec.checkCapAt (.threadCap t.bv) ssl
              (Fl4Spec.capInsert (absCap nc) (ps.bv, idxs) (t.bv, Fl4Spec.tcbCnodeIndex n)))))).run σ1 =
              ({(.ok (), σ')}, False) ∧
          res.1 = .Ok () ∧ DState (L := L) Z.th res.2.1 σ' G' ∧
          (∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
            capV (L.mem res.2.1) y = capV (L.mem s1) y) ∧
          (capV (L.mem res.2.1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null ∨
            capV (L.mem res.2.1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = nc) ∧
          W res.2.1 res.2.2 σ' G' ⦄ := by
    intro s1 a1 σ1 G1 hDS1 hW1 hroot hczs
    refine WP.spec_mono (WP.spec_and (install_after Z.th hP s0 s1 a1 σ1 G1 hDS1 t ht n hn hroot ssl hAs nc hwf hcv he
      hfw hps hls hczs hsrc0 hsh hbd hkey hv)
      (install_after_frame hP s1 a1 hDS1.1.2.2.1 hDS1.2.1 t (cslotAddr ssl) nc hAsrc.isSlot hAt.isSlot)) ?_
    rintro res ⟨⟨σ', G', hrun, hr1, ha1, hDS', hcap, hst, htg, hcase⟩, hF⟩
    refine ⟨σ', G', hrun, hr1, hDS', hcap, htg, ?_⟩
    rcases hcase with ⟨e1, e2, e3⟩ | ⟨hins, hthr, hsrc1, hnn, hnut, hdst⟩
    · rw [ha1, e1, e2, e3]; exact hW1
    obtain ⟨V1, Ac1, Lst1, D1, J1, hkb1, hns1, hsg1, hp1⟩ := hI.wjr _ _ _ _ hW1
    have hsg' : SpecGlob σ' := by
      obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS1.1.1.abs_cap hAsrc
      have e0 : c0 = srcC0 := by rw [← hsrc1, capV_of_capAt hc0]
      have ha0 := (getCap_set_iff σ1 _ _ _).1 (congrArg Prod.fst hg0)
      rw [hca0.abs, e0] at ha0
      exact hsg1.insTcb hins hnut hsh ha0
    have hwS := SlotFrame2.writesIn hF
    obtain ⟨Ac2, Lst2, D2, J2⟩ := J1.insTJ (fun e => absurd e hn2) ht hn hins hDS' hst hwS hroot hcap
      (by rw [hdst]; exact hnut) (by rw [hdst]; exact hnn) ⟨_, hAsrc.isSlot, by rw [hdst, hsrc1]; exact hsh⟩
      (fun h3 => by rw [hdst]; exact Or.inr (hep h3 hnn)) (fun e => absurd e hn2) ⟨_, hAs.isSlot, hthr⟩
      (fun P L4 L3 L2 L1 h => by
        rw [hdst]; exact h.copy hAsrc.isSlot (by rw [hsrc1]; exact hv) (by rw [hsrc1]; exact htu))
      (fun U h => by rw [hdst]; exact (h _ hAsrc.isSlot).of_okey (by rw [hsrc1]; exact hkey))
      (fun h => by rw [hdst]; exact hnat (by rw [← hsrc1]; exact h _ hAsrc.isSlot))
    have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap nc) (ps.bv, idxs)
        (t.bv, Fl4Spec.tcbCnodeIndex n) σ1).1 := by rw [hins]; rfl
    have hcn := capInsert_nkn _ _ _ σ1 _ hmem
    have hact : σ'.schedulerAction = σ1.schedulerAction := by
      have e := congrArg Fl4Spec.AbstractState.schedulerAction hcn.1; exact e
    rw [ha1]
    exact hI.ins s1 res.2.1 a1 σ1 σ' G1 G' t n _ _ hDS1 hW1 hDS'
      ⟨V1, Ac2, Lst2, D2, J2, by rw [hwS.1]; exact hkb1, fun u e => hns1 u (hact ▸ e), hsg',
        hp1.of_ppk (PPK.of_cnK hcn)⟩ ht hn hins hwS hroot hcap (by rw [hdst]; exact hnn)
      ⟨_, hAsrc.isSlot, by rw [hdst, hsrc1]; exact hsh⟩ ⟨_, hAs.isSlot, hthr⟩
  unfold tcb.install_tcb_cap
  rw [spec_eq_ok (tcb_slot_spec t idx), tcb_root_eq t idx hn hidx]
  simp only [bind_ok]
  obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAt
  by_cases hc0n : c0 = .Null
  · subst hc0n
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    refine WP.spec_mono (after s a σ G hDS hW (by rw [capV_of_capAt hc0]) hczs0) ?_
    rintro res ⟨σ', G', hrun, hr1, hDS', hcap, htg, hW'⟩
    have hg0' : Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({(.nullCap, σ)}, False) := by
      rw [hg0, hca0.abs]; rfl
    exact ⟨⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok (by rw [capDelete_null hg0']; rfl) (mem_of_run hrun),
      hcz0.install hP ht hn (fun y hy hne => ChgZ.of_eq (hcap y hy hne)) htg hAsrc.isSlot hsh0 hep, hW'⟩, hDS'⟩,
      fun _ y hy hne => hcap y hy hne⟩
  · have hcapNE : obj.Slot.cap st (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) s ⦃ c => P1.NullOrEp H c ⦄ := by
      rw [slot_cap_eq, capAt_capV]; exact (WP.spec_ok _).2 hnoe
    apply WP.spec_bind (WP.spec_and (delete_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 _ hAt s a σ G
      hDS hW (by rw [capV_of_capAt hc0]; exact hc0n) (hDE.2.1 G hDS.1.2.2.1))
      (P1.cdt.delete.ep (ar := arI) s a _ J0.blk hcapNE
        (P := fun s2 => ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
          capV (L.mem s2) y = capV (L.mem s) y)
        (fun s1 a1 hag => WP.spec_mono (empty_capV_frame (arI := arI) hP (J0.slotCapW (tLowSlots_all _))
          hDS.1.2.2.1 hAt.isSlot s1 a1 hag) fun r h => h)))
    rintro ⟨r, s1, a1⟩ ⟨⟨σ1, G1, hDS1, -, -, hmD, hcase, hW1⟩, -, -, -, hfr⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD hW1 ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_mono (after s1 a1 σ1 G1 hDS1 hW1 hnull (hczs0.trans (hcz _ hAsrc.isSlot (hsrcT n hn)))) ?_
      rintro res ⟨σ', G', hrun, hr1, hDS', hcap, htg, hW'⟩
      exact ⟨⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok hmem (mem_of_run hrun),
        hcz0.install hP ht hn (fun y hy hne => (hcz y hy hne).trans (ChgZ.of_eq (hcap y hy hne))) htg
          hAsrc.isSlot hsh0 hep, hW'⟩, hDS'⟩, fun _ y hy hne => (hcap y hy hne).trans (hfr rfl y hy hne)⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem, hW1⟩, hDS1⟩, fun h => by cases h⟩



/-- `install_fhJM` with the new cap's conditions as `NewCapOK` (as `install_okJM`). -/
theorem install_fhOkJM [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJPM (L := L) arI AR MR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (hn2 : n ≠ 2) (idx : U64) (hidx : idx.val = n)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (nc : capability.Cap) (sl : Fl4Spec.CslotPtr) (hok : NewCapOK Z.th (L.mem s0) nc sl)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4)
    (hnoe : P1.NullOrEp H (capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)))) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr sl) ⦃ res =>
      InstPostWP (L := L) W (WJPM (L := L) arI AR MR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, sl))) s0 σ res ∧
      (res.1 = .Ok () → ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
        capV (L.mem res.2.1) y = capV (L.mem s) y) ⦄ := by
  obtain ⟨ps, rs, hps, h1s, hls, hwf, hcv, he, hfw, hsh, hbd, hkey, hvk, htu, hnat⟩ := hok
  obtain ⟨sa, idxs⟩ := sl
  simp only at h1s hls; subst h1s
  exact install_fhJM arI hI hH s0 s a σ G hDS hW t ht n hn hn2 idx hidx hcz0 ssl hAs nc hwf hcv he hfw hps hls rfl
    hsh hbd hkey hvk htu hnat hep hnoe

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **The TCB installs' invariants at every kernel-state base** (module
docstring): `InsWJ` and the deletion loop's steps (`DelHypsWRZ`) at `W kb`. -/
structure TcbInsWM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) : Prop where
  ins : ∀ kb, InsWJ (L := L) arI AR Z H Cs kb (W kb)
  del : ∀ kb, DelHypsWRZ (L := L) arI (W kb) (WJPM (L := L) arI AR MR Z H Cs kb) Rd Rz Z.th

/-- **The caller's restart at the installs' invariant**: `JAtZ.restartWJR`
with `W` after it (`RestartWJ`), at the kernel-state base after. -/
theorem JAtZ.restartWM {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop} {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop}
    (hI : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz)
    (hR : ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → W (L.ksb s) s1 ar σ1 Z.G) :
    ∃ s1 σ1, tcb.restart_caller st s = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      DState (L := L) Z.th s1 σ1 Z.G ∧ W (L.ksb s1) s1 ar σ1 Z.G ∧
      SlotsSame Z.th (L.mem s) (L.mem s1) := by
  obtain ⟨s1, σ1, hrc, hst1, hDS1, -, hS1⟩ := J.restartWJR arI hni hsg hP0 hct
  obtain ⟨s1', σ1', -, hrc', hst1', -, -, -, -, -, -, hs1', -⟩ := J.restartJ hni hct
  have es : s1' = s1 := Result.ok_injective (hrc'.symm.trans hrc)
  have eσ : σ1' = σ1 :=
    (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (hst1'.symm.trans hst1)))).2
  subst es eσ
  have hW := hR s1' σ1' hs1' hst1
  obtain ⟨-, -, -, -, -, hkb, -⟩ := (hI.ins _).wjr _ _ _ _ hW
  exact ⟨s1', σ1', hrc, hst1, hDS1, by rw [hkb]; exact hW, hS1⟩

set_option maxHeartbeats 8000000 in
/-- **The SetTimeoutEndpoint label at `JAt`** (`JAtPre` if preempted), as
TcbCtl's `tcb_set_timeout_refinesW`: the decode, the caller's restart
(`JAtZ.restartWJR`), the timeout handler's install by `thread_control_capsJM`
at the deletion loop's steps (`DelHypsWR` at `WJR`), `top_of_instJM`. -/
theorem tcb_set_timeoutJM [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTimeoutEndpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (args : List Fl4Spec.Data) (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ fl4_abi.label.TCBSetTimeoutEndpoint p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl args ci ssl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl args ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKXP
  rw [decode_timeout_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_timeout_endpoint tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetTimeoutEp
    rw [whenE_pos (by omega)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 0#u64 := by scalar_tac
  simp only [h0, ↓reduceIte, if_pos hge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, slot_cap_eq,
    capAt_capV, vfh_eq]
  have hspec0 : ∀ v : Prop, [Decidable v] → v = Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0)) →
      (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps).run σ =
        (Fl4Spec.checkHandlerEp (Z := Unit) 1 e >>= fun handler =>
          Fl4Spec.NonDetE.returnOk (.threadControlCaps p.bv ssl none (some handler) none none none)).run σ := by
    intro v _ _
    unfold Fl4Spec.decodeSetTimeoutEp
    rw [whenE_neg (by have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega),
      retOk_bind, retOk_bind, he, the_some]
    rfl
  by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0))
  · rw [decide_eq_true hv]; simp only [↓reduceIte]
    obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartWM arI hni hsg hP0 hct hHp (hR ct hct)
    rw [hrc]; simp only [bind_ok]
    have hxs : IsSlot Z.th x0 := by rw [hxe]; exact AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.ok (tcInv p ssl tcb.UPDATE_TIMEOUT (.Null, (0, [])) (capV (L.mem s) x0, e.2) (.Null, (0, []))
          (.Null, (0, [])) (0 : BitVec 64) none), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec0 _ rfl]
      unfold Fl4Spec.checkHandlerEp
      rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he1]; exact hv)]
      show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e) >>= _).run σ = _
      rw [retOk_bind, retOk_bind]
      obtain ⟨e1, e2⟩ := e
      simp only at he1
      subst he1
      simp only [tcInv, optArg, flags_T, ↓reduceIte]
      rfl
    have hnf := vfh_not_frame hv
    have hc1 : capV (L.mem s1) x0 = capV (L.mem s) x0 := hS1.capV hxs
    have hU0 : (tcb.UPDATE_TIMEOUT &&& tcb.UPDATE_IPC_BUFFER) = 0#u64 := by
      simp only [tcb.UPDATE_TIMEOUT, tcb.UPDATE_IPC_BUFFER]; decide
    have hT' := thread_control_capsJM arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs tcb.UPDATE_TIMEOUT
      (.Null, (0, [])) (capV (L.mem s) x0, e.2) (.Null, (0, [])) (.Null, (0, [])) (fun h => (Eq.mp flags_T.1 h).elim)
      (fun _ => by
        show NewCapOK Z.th (L.mem s1) (capV (L.mem s) x0) e.2
        rw [← hc1, hxe]
        exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps hps1 (by rw [← hxe, hc1]; exact hnf))
      (fun h => (Eq.mp flags_T.2.2.1 h).elim) (fun h => (Eq.mp flags_T.2.2.1 h).elim) (fun _ h => absurd rfl h)
      0#u64 0 (fun h => absurd hU0 h) .Null none (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    simp only [cslot_zero, ← hxe] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instJM arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
  · rw [decide_eq_false hv]; simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_,
      Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec0 _ rfl]
    unfold Fl4Spec.checkHandlerEp
    rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he1]; exact hv)]
    exact run_bind_error (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
      Fl4Spec.SEMonad Unit Unit)) rfl _) _


set_option maxHeartbeats 16000000 in
/-- **The SetSpace label at `JAt`** (`JAtPre` if preempted), as TcbCtl's
`tcb_set_space_refinesW`: the decode (the roots by `roots_rel`), the
caller's restart (`JAtZ.restartWJR`), the fault handler's and the roots'
installs by `thread_control_capsJM`, `top_of_instJM`. -/
theorem tcb_set_spaceJM [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSpace)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ fl4_abi.label.TCBSetSpace p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hP := J.xtop.rel.1
  have hDS : DState (L := L) Z.th s σ Z.G := J.dstate
  unfold TcbOKXP
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetSpace (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_space_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 2 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR)
        (JAtPreMV (L := L) arI AR MR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSpace (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetSpace
    rw [whenE_pos (by simpa using h)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  unfold tcb.decode_set_space tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 2#u64 ↔ 2 ≤ args.length := by
    show length >= 2#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 2 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hX.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hX.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hl with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hX.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hX.get hx2' h2
  have hexc : excaps = [e0, e1, e2] := by
    have h3 := hX.1
    match excaps, he0, he1, he2, h3 with
    | [a, b, c], h0', h1', h2', _ => simp at h0' h1' h2'; rw [h0', h1', h2']
  subst hexc
  subst hxe1 hxe2
  obtain ⟨r, hr, hcase⟩ := roots_rel Z.th hP s σ Z.G hDS p hp y0 y1 e1 e2 he11 ⟨ps1, hps1, hps11⟩ he21
    ⟨ps2, hps2, hps21⟩ (hnc _ (by simp) e1.2 ⟨ps1, hps11, Or.inl hps1⟩ rfl) (hnc _ (by simp) e2.2 ⟨ps2, hps21, Or.inl hps2⟩ rfl) ssl
  rw [hr]
  have hspec : (Fl4Spec.decodeSetSpace (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      [e0, e1, e2]).run σ =
      (Fl4Spec.decodeCvSpace (Z := Unit) [y0.bv, y1.bv] (.threadCap p.bv) ssl [e1, e2] >>= fun space =>
        Fl4Spec.checkHandlerEp (Z := Unit) 1 e0 >>= fun fh =>
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl (some fh) none
            space.tcNewCroot space.tcNewVroot none)).run σ := by
    unfold Fl4Spec.decodeSetSpace
    rw [whenE_neg (by simp), retOk_bind]
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.getElem?_cons_zero, the_some, retOk_bind]
    rfl
  rcases hcase with ⟨cc, vc, rfl, hcv, hokc, hokv⟩ | ⟨e, e', rfl, hcv, herr⟩
  · simp only [slot_cap_eq, capAt_capV, vfh_eq, bind_ok]
    rw [run_bind_ok hcv] at hspec
    by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0))
    · rw [decide_eq_true hv]; simp only [↓reduceIte, lift, bind_ok]
      obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartWM arI hni hsg hP0 hct hHp (hR ct hct)
      rw [hrc]; simp only [bind_ok]
      have hxs : IsSlot Z.th x0 := by rw [hxe0]; exact AbsSlot.isSlot ⟨ps0, hps01, Or.inl hps0⟩
      have hc1 : capV (L.mem s1) x0 = capV (L.mem s) x0 := hS1.capV hxs
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSpace (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            [e0, e1, e2])).run σ =
          ({(.ok (tcInv p ssl (tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) (capV (L.mem s) x0, e0.2) (.Null, (0, []))
            (cc, e1.2) (vc, e2.2) (0 : BitVec 64) none), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he01]; exact hv)]
        show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e0) >>= _).run σ = _
        rw [retOk_bind, retOk_bind]
        obtain ⟨e01, e02⟩ := e0
        simp only at he01
        subst he01
        simp only [optArg, flags_SF, ↓reduceIte]
        rfl
      have hU0 : ((tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) &&& tcb.UPDATE_IPC_BUFFER) = 0#u64 := by
        simp only [tcb.UPDATE_SPACE, tcb.UPDATE_FAULT, tcb.UPDATE_IPC_BUFFER]; decide
      have hT' := thread_control_capsJM arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs
        (tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT)
        (capV (L.mem s) x0, e0.2) (.Null, (0, [])) (cc, e1.2) (vc, e2.2)
        (fun _ => by
          show NewCapOK Z.th (L.mem s1) (capV (L.mem s) x0) e0.2
          rw [← hc1, hxe0]
          exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps0 hps01 (by rw [← hxe0, hc1]; exact vfh_not_frame hv))
        (fun h => (Eq.mp flags_SF.2.1 h).elim) (fun _ => hokc.of_same hS1) (fun _ => hokv.of_same hS1)
        (fun _ => vfh_ep hv) 0#u64 0 (fun h => absurd hU0 h) .Null none (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      simp only [cslot_zero, ← hxe0, bufArg] at hT'
      exact WP.spec_mono hT' (fun res h => top_of_instJM arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
    · rw [decide_eq_false hv]; simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
      refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_,
        Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec]
      unfold Fl4Spec.checkHandlerEp
      rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he01]; exact hv)]
      exact run_bind_error (run_bind_error (m := (Fl4Spec.NonDetE.throwError
        (Fl4Spec.SyscallError.invalidCapability 1) : Fl4Spec.SEMonad Unit Unit)) rfl _) _
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨e', ?_, herr⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error hcv _


set_option maxHeartbeats 16000000 in
/-- **The SetIPCBuffer label at `JAt`** (`JAtPre` if preempted), as TcbCtl's
`tcb_set_ipc_refinesW`: the decode (the buffer's frame cap derived and
checked), the caller's restart (`JAtZ.restartWJR`), the buffer's install by
`thread_control_capsJM` (`install_bufferJM`, the IPC-buffer word and the tail
at `WJR` by `bufHypW_J`), `top_of_instJM`. -/
theorem tcb_set_ipcJM [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetIPCBuffer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hfnz : FrNZ Z.th (L.mem s))
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ fl4_abi.label.TCBSetIPCBuffer p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hDS : DState (L := L) Z.th s σ Z.G := J.dstate
  unfold TcbOKXP
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_ipc_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_ipc_buffer tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  -- the truncated cases
  have htr : args = [] ∨ excaps = [] →
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.error .truncatedMessage, σ)}, False) := by
    intro h
    apply run_liftME_err
    unfold Fl4Spec.decodeSetIpcBuffer
    by_cases ha : args = []
    · subst ha
      rw [whenE_pos (by simp)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · have he : excaps = [] := h.resolve_left ha
      subst he
      rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (by simp)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
  have htrS : (args = [] ∨ excaps = []) → TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) σ
      blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s
        (.Err (.Sys .TruncatedMessage), s, ar) := fun h =>
    TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, htr h, Or.inl trivial⟩, hJ0⟩
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (htrS (Or.inr (List.eq_nil_of_length_eq_zero (by omega))))
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  by_cases h1 : length < 1#u64
  · have hge : ¬ (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 := by
      show ¬ length >= 1#u64; scalar_tac
    simp only [h0, ↓reduceIte, if_neg hge, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (htrS (Or.inl ?_))
    exact List.eq_nil_of_length_eq_zero (by scalar_tac)
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 := by
    show length >= 1#u64; scalar_tac
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  simp only [h0, ↓reduceIte, if_pos hge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  -- the spec, up to the buffer
  obtain ⟨e1, e2⟩ := e
  simp only at hxe he1 hps hps1
  subst he1 hxe
  have hspec : (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ =
      ((if y0.bv = 0 then Fl4Spec.NonDetE.returnOk none else do
          let bc ← Fl4Spec.deriveCap (Z := Unit) e2 (absCap (capV (L.mem s) (cslotAddr e2)))
          Fl4Spec.checkValidIpcBuffer y0.bv bc
          Fl4Spec.NonDetE.returnOk (some (bc, e2)) : Fl4Spec.SEMonad Unit _) >>= fun nb =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none none none
          (some (y0.bv, nb)))).run σ := by
    unfold Fl4Spec.decodeSetIpcBuffer
    have hne : excaps ≠ [] := List.ne_nil_of_mem (List.mem_of_getElem? he)
    rw [whenE_neg (by simp), retOk_bind, whenE_neg (by simpa using hne), retOk_bind, retOk_bind]
    rw [show (List.map UScalar.bv (y0 :: rest))[0]? = some y0.bv from rfl, the_some, retOk_bind, he, the_some]
    rfl
  obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartWM arI hni hsg hP0 hct hHp (hR ct hct)
  have hxs : IsSlot Z.th (cslotAddr e2) := AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
  have hc1 : capV (L.mem s1) (cslotAddr e2) = capV (L.mem s) (cslotAddr e2) := hS1.capV hxs
  have hcwf := slot_wf hDS.1.1 hps hps1
  have hcv0 : CapValid Z.th (capV (L.mem s) (cslotAddr e2)) :=
    hDS.1.2.1.abs ⟨ps, hps1, Or.inl hps⟩ (capAt_capV _ _)
  have hB : (tcb.UPDATE_IPC_BUFFER &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 →
      BufHypW (L := L) (W (L.ksb s1)) Z.th p y0 y0.bv :=
    fun _ => (hHp.ins (L.ksb s1)).buf p hp y0
  by_cases hy : y0 = 0#u64
  · -- no frame
    have hy' : y0.bv = 0 := by rw [hy]; rfl
    have hdfb : tcb.derive_for_buffer st s y0 (cslotAddr e2) = ok (.Ok (capV (L.mem s) (cslotAddr e2), 0#u64)) := by
      unfold tcb.derive_for_buffer; rw [if_pos hy]; simp [slot_cap_eq, capAt_capV]
    rw [hdfb]; simp only [bind_ok, hrc]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.ok (tcInv p ssl tcb.UPDATE_IPC_BUFFER (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, []))
          (.Null, (0, [])) y0.bv none), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec, if_pos hy', retOk_bind]
      simp only [tcInv, optArg, flags_B, ↓reduceIte, frameOf]
      rfl
    have hT' := thread_control_capsJM arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs tcb.UPDATE_IPC_BUFFER
      (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, [])) (fun h => (Eq.mp flags_B.1 h).elim)
      (fun h => (Eq.mp flags_B.2.1 h).elim) (fun h => (Eq.mp flags_B.2.2.1 h).elim)
      (fun h => (Eq.mp flags_B.2.2.1 h).elim) (fun _ h => absurd rfl h) y0 y0.bv hB
      (capV (L.mem s) (cslotAddr e2)) none (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    simp only [cslot_zero, bufArg] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instJM arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
  -- a frame: derived and checked
  have hy' : ¬ y0.bv = 0 := fun h => hy (UScalar.eq_of_val_eq (by
    have := congrArg BitVec.toNat h; simpa using this))
  unfold tcb.derive_for_buffer
  rw [if_neg hy]
  simp only [slot_cap_eq, capAt_capV, bind_ok]
  generalize capV (L.mem s) (cslotAddr e2) = c0 at hcwf hcv0 hc1 hnc hspec ⊢
  obtain ⟨r, hr, r', hr', hrel⟩ := derive_rel (st := st) s σ (cslotAddr e2) e2 c0
    hcwf.1 hcwf.2 (fun h => hnc e2 ⟨ps, hps1, Or.inl hps⟩ rfl (by cases c0 <;> simp_all [isUt]))
  simp only [hr, bind_ok]
  cases r with
  | Err er =>
    cases r' with
    | ok _ => exact hrel.elim
    | error er' =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨er', ?_, Or.inl hrel⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec, if_neg hy']
      exact run_bind_error (run_bind_error hr' _) _
  | Ok c' =>
    cases r' with
    | error _ => exact hrel.elim
    | ok a =>
      obtain ⟨hwf', ha, hev', hcv', -⟩ := hrel
      obtain ⟨rc, hrc', hcase⟩ := Vs.check_valid_ipc_buffer_rel y0 c' σ
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hrc']
      rcases hcase with ⟨rfl, hck⟩ | ⟨er, er', rfl, hmer, hck⟩
      · simp only [bind_ok, hrc]
        obtain ⟨q, sz, rr, m, ep, aa, va, rfl⟩ := check_ok_frame hrc'
        obtain ⟨rfl, m0, ep0, a0, va0, hc0⟩ := derive_frame_inv (fun h => ⟨_, hnc e2 ⟨ps, hps1, Or.inl hps⟩ rfl h⟩) hr
        have hcvc : CapValid Z.th (capability.Cap.Frame q sz rr false m false aa va) := hcv' Z.th hcv0
        have hok : NewCapOK Z.th (L.mem s1) (.Frame q sz rr false m false aa va) e2 := by
          refine ⟨ps, _, hps, hps1, rfl, hwf', hcvc, hev', fun _ => frame_so_refl hcvc, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hc1, hc0]; rfl
          · rw [hc1, hc0]; exact Or.inl rfl
          · rw [hc1, hc0]; rfl
          · rw [hc1]; exact derive_vcap hr
          · exact fun h => False.elim h
          · exact fun _ => by simp [Vs.NativeCap]
        have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)).run σ =
            ({(.ok (tcInv p ssl tcb.UPDATE_IPC_BUFFER (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, []))
              (.Null, (0, [])) y0.bv (some (.Frame q sz rr false m false aa va, e2))), σ)}, False) := by
          apply run_liftME_ok
          rw [← ha] at hr'
          have hin : ((do
              let bc ← Fl4Spec.deriveCap (Z := Unit) e2 (absCap c0)
              Fl4Spec.checkValidIpcBuffer y0.bv bc
              Fl4Spec.NonDetE.returnOk (some (bc, e2)) : Fl4Spec.SEMonad Unit _)).run σ =
              ({(.ok (some (absCap (.Frame q sz rr false m false aa va), e2)), σ)}, False) := by
            rw [run_bind_ok hr', run_bind_ok hck]; rfl
          rw [hspec, if_neg hy', run_bind_ok hin]
          simp only [tcInv, optArg, flags_B, ↓reduceIte, frameOf]
          rfl
        have hT' := thread_control_capsJM arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs
          tcb.UPDATE_IPC_BUFFER (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, []))
          (fun h => (Eq.mp flags_B.1 h).elim) (fun h => (Eq.mp flags_B.2.1 h).elim)
          (fun h => (Eq.mp flags_B.2.2.1 h).elim) (fun h => (Eq.mp flags_B.2.2.1 h).elim) (fun _ h => absurd rfl h)
          y0 y0.bv hB .Null (some (.Frame q sz rr false m false aa va, e2)) (fun c sl h => by cases h; exact hok)
          (fun c sl h => by cases h; exact ⟨⟨q, sz, rr, m, aa, va, rfl⟩, Vs.check_valid_ipc_buffer_al hrc'⟩)
          (fun _ _ _ => hfnz.of_same hS1)
        simp only [cslot_zero, bufArg] at hT'
        exact WP.spec_mono hT' (fun res h => top_of_instJM arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
      · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, bind_ok]
        refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨er', ?_, ErrRel.of_map hmer⟩, hJ0⟩)
        apply run_liftME_err
        rw [hspec, if_neg hy']
        rw [← ha] at hr'
        exact run_bind_error ((run_bind_ok hr' _).trans (run_bind_error hck _)) _


set_option maxHeartbeats 16000000 in
/-- **The Configure label at `JAt`** (`JAtPre` if preempted), as TcbCtl's
`tcb_configure_refinesW`: the decode (the buffer by `buf_rel`, the roots by
`roots_rel`), the caller's restart (`JAtZ.restartWJR`), the roots' and the
buffer's installs by `thread_control_capsJM` (the buffer's word and tail at
`WJR` by `bufHypW_J`), `top_of_instJM`. -/
theorem tcb_configureJM [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbConfigure)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hfnz : FrNZ Z.th (L.mem s))
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ fl4_abi.label.TCBConfigure p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hP := J.xtop.rel.1
  have hDS : DState (L := L) Z.th s σ Z.G := J.dstate
  unfold TcbOKXP
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeTcbConfigure (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_configure_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 3 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR)
        (JAtPreMV (L := L) arI AR MR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeTcbConfigure (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeTcbConfigure
    by_cases ha : args.length < 3
    · rw [whenE_pos (by simpa using ha)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (h.resolve_left ha)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
  unfold tcb.decode_configure tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 3#u64 ↔ 3 ≤ args.length := by
    show length >= 3#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 3 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hX.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hX.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, y2, rest, rfl⟩ : ∃ y0 y1 y2 rest, args = y0 :: y1 :: y2 :: rest := by
    match args, hl with
    | y0 :: y1 :: y2 :: rest, _ => exact ⟨_, _, _, _, rfl⟩
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  have ha2 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 2#u64 = ok y2 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 2#u64 y2 (by simp)
  rw [ha0, ha1, ha2]; simp only [bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hX.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hX.get hx2' h2
  have hexc : excaps = [e0, e1, e2] := by
    have h3 := hX.1
    match excaps, he0, he1, he2, h3 with
    | [a, b, c], h0', h1', h2', _ => simp at h0' h1' h2'; rw [h0', h1', h2']
  subst hexc
  subst hxe0 hxe1 hxe2
  have hspec : (Fl4Spec.decodeTcbConfigure (Z := Unit) ((y0 :: y1 :: y2 :: rest).map UScalar.bv) (.threadCap p.bv)
      ssl [e0, e1, e2]).run σ =
      (Fl4Spec.decodeSetIpcBuffer (Z := Unit) [y2.bv] (.threadCap p.bv) ssl [e2] >>= fun sp =>
        Fl4Spec.decodeCvSpace (Z := Unit) [y0.bv, y1.bv] (.threadCap p.bv) ssl [e0, e1] >>= fun ss =>
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none
            ss.tcNewCroot ss.tcNewVroot sp.tcNewBuffer)).run σ := by
    unfold Fl4Spec.decodeTcbConfigure
    rw [whenE_neg (by simp), retOk_bind, whenE_neg (by simp), retOk_bind]
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.getElem?_cons_succ,
      List.getElem?_cons_zero, the_some, retOk_bind]
    rfl
  obtain ⟨rb, hrb, hbcase⟩ := buf_rel Z.th s σ Z.G hDS y2 e2 he21 ⟨ps2, hps2, hps21⟩ (hnc _ (by simp) e2.2 ⟨ps2, hps21, Or.inl hps2⟩ rfl)
  rw [hrb]
  rcases hbcase with ⟨bc0, bfr, rfl, hbs, hbok, hbfd⟩ | ⟨er, er', rfl, hbs, herr⟩
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨er', ?_, herr⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error ((ipc_spec σ p.bv ssl y2.bv [] e2 []).trans (run_bind_error hbs _)) _
  simp only [bind_ok]
  have hip : (Fl4Spec.decodeSetIpcBuffer (Z := Unit) [y2.bv] (.threadCap p.bv) ssl [e2]).run σ =
      ({(.ok (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none none none (some (y2.bv, frameOf bfr))),
        σ)}, False) :=
    (ipc_spec σ p.bv ssl y2.bv [] e2 []).trans ((run_bind_ok hbs _).trans rfl)
  rw [run_bind_ok hip] at hspec
  obtain ⟨r, hr, hcase⟩ := roots_rel Z.th hP s σ Z.G hDS p hp y0 y1 e0 e1 he01 ⟨ps0, hps0, hps01⟩ he11
    ⟨ps1, hps1, hps11⟩ (hnc _ (by simp) e0.2 ⟨ps0, hps01, Or.inl hps0⟩ rfl) (hnc _ (by simp) e1.2 ⟨ps1, hps11, Or.inl hps1⟩ rfl) ssl
  rw [hr]
  rcases hcase with ⟨cc, vc, rfl, hcv, hokc, hokv⟩ | ⟨e, e', rfl, hcv, herr⟩
  · simp only [lift, bind_ok]
    rw [run_bind_ok hcv] at hspec
    obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartWM arI hni hsg hP0 hct hHp (hR ct hct)
    rw [hrc]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeTcbConfigure (Z := Unit) ((y0 :: y1 :: y2 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
          [e0, e1, e2])).run σ =
        ({(.ok (tcInv p ssl (tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) (.Null, (0, [])) (.Null, (0, []))
          (cc, e0.2) (vc, e1.2) y2.bv bfr), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec]
      simp only [tcInv, optArg, flags_SB, ↓reduceIte]
      rfl
    have hT' := thread_control_capsJM arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs
      (tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) (.Null, (0, [])) (.Null, (0, [])) (cc, e0.2) (vc, e1.2)
      (fun h => (Eq.mp flags_SB.1 h).elim) (fun h => (Eq.mp flags_SB.2.1 h).elim)
      (fun _ => hokc.of_same hS1) (fun _ => hokv.of_same hS1) (fun _ h => absurd rfl h) y2 y2.bv
      (fun _ => (hHp.ins (L.ksb s1)).buf p hp y2) bc0 bfr (fun c sl h => (hbok c sl h).of_same hS1) hbfd
      (fun _ _ _ => hfnz.of_same hS1)
    simp only [cslot_zero] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instJM arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨e', ?_, herr⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error hcv _


set_option maxHeartbeats 32000000 in
/-- **SetSchedParams after its checks at `J`** (as XTopTcbSched's `ssp_tailX`):
the caller's restart (`JAtZ.restartWJR`), the fault handler's install at the
deletion loop's invariant (`install_fhOkJM`, `JAtPre` when preempted; the
other slots' caps kept), then `set_mcp` (`JAtZ.mcpWrJ`), `set_priority`
(`JAtZ.setPrioJS`, the current thread's facts by `JAtZ.prioCur` from
`CurInv`) and the SC step: none, `unbind_tcb` (`JAtZ.unbindTcbJ`) or
`bind_tcb` (`JAtZ.bindTcbJ`, the decode's checks carried: `SpecPost` by
`specPost_restart`, `specPost_install`, `BindOK.after`; the SC and the
release check by `install_sched`). -/
theorem ssp_tailJM [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (hAT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)
    (p : U64) (hp : Z.th p = some .tcb) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl) (hpsl : capV (L.mem s) (cslotAddr ssl) = .Thread p)
    (x2 : U64) (e2 : Fl4Spec.Cap × Fl4Spec.CslotPtr)
    (hxe2 : x2 = cslotAddr e2.2) (he21 : e2.1 = absCap (capV (L.mem s) x2)) (ps : U64)
    (hps : Z.th ps = some (.cnode e2.2.2.length)) (hps1 : e2.2.1 = ps.bv)
    (hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x2)))
    (y0 y1 scv : U64) (hy0 : y0.val < 256) (hy1 : y1.val < 256) (scf : Bool) (q : Fl4Spec.ObjRef)
    (sco : Option (Option Fl4Spec.ObjRef)) (h1 : sco = none ↔ scf = false) (h2 : sco = some none → scv = 0#u64)
    (h3 : ∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64)
    (hD : ScDec σ p.bv sco) (hpI : p ≠ L.idleW s)
    (hscs : scv ≠ 0#u64 → ∃ xs sb, IsSlot Z.th xs ∧ capV (L.mem s) xs = .SchedContext scv sb)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (hdec : DecOut m σ (.invokeTCB (.threadControlSched p.bv ssl (some e2) (some (Fl4Spec.ucast 8 y0.bv, q))
      (some (Fl4Spec.ucast 8 y1.bv, q)) sco)))
    (blk call don : Bool) :
    (do
      let s1 ← tcb.restart_caller st s
      tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (capV (L.mem s) x2, x2) y0 y1 scv
        (if scf then (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT ||| tcb.SCHED_UPDATE_SC)
          else (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT))) ⦃ res =>
      TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) σ blk call don m s res ⦄ := by
  have hpT : p ∈ Z.T := J.thT p hp
  obtain ⟨hcur, xc, hkc, hrunc⟩ := J.curRunnable hni hct
  obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartWM arI hni hsg hP0 hct hHp (hR ct hct)
  obtain ⟨s1', σ1', xc', hrc', hst1', hkc', -, e1, -, hid1, hct1, -, -⟩ := J.restartJ hni hct
  have es : s1' = s1 := Result.ok_injective (hrc'.symm.trans hrc)
  have eσ : σ1' = σ1 :=
    (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (hst1'.symm.trans hst1)))).2
  subst es eσ
  rw [hkc] at hkc'; cases hkc'
  have hst1c : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1')}, False) := by
    rw [← hcur]; exact hst1
  have hC0 := J.curInv (by rw [hni.2]; intro h; cases h)
  have hC1 : Sched.CurInv σ1' := by
    have h := hC0.restart (xt := xc) (by rw [hcur]; exact hkc)
    rw [hcur] at h; rw [e1]; exact h
  have htm1 : σ1'.curTime = σ.curTime := by rw [e1]; unfold Notif.stsAct; split_ifs <;> rfl
  -- the decode's checks of the target, after the restart
  obtain ⟨xp, hkp, hDU, hDB⟩ := hD
  obtain ⟨xt0, hkt0, hxs0, -⟩ := hC0.tcb
  have hpc : ∀ v, sco = some (some v) → p.bv ≠ σ.curThread := fun v e hpe => by
    rw [hpe, hkt0] at hkp; cases hkp; rw [(hDB v e).1] at hxs0; cases hxs0
  have hBI : BlkIn σ p.bv xp.tcbState := fun e he => by
    rcases epBlocked_some he with ⟨d, hst⟩ | ⟨ro, d, hst⟩
    · exact J.sv.sendQ _ _ e d hkp hst
    · exact J.sv.recvQ _ _ e ro d hkp hst
  have hpost1 := specPost_restart J.inv hkc hrunc hst1c ⟨xp, hkp, hDU, hDB⟩
    (fun x hx => by rw [hkp] at hx; cases hx; exact ⟨blkQ_of_sv J.sv hkp, hBI⟩) hpc
  -- the old fault handler at the restart: null or an endpoint cap
  obtain ⟨V1, Ac1, Lst1, D1, J1, -⟩ := (hHp.ins _).wjr _ _ _ _ hW1
  obtain ⟨Tr1, Cq1, hJ1⟩ := J1.jpl
  have hnoe : P1.NullOrEp H (capV (L.mem s1') (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3))) := hJ1.fhSlot p hp
  obtain ⟨xp1, hkp1, -⟩ := id hpost1
  obtain ⟨c, a', hca, hCR, hg⟩ := hDS1.1.1.abs_cap (sl := (p.bv, Fl4Spec.tcbCnodeIndex 3))
    ⟨p, rfl, Or.inr ⟨hp, 3, by decide, rfl⟩⟩
  rw [getCap_tcb_three hkp1] at hg
  have ha' : xp1.tcbFaultHandler = a' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hg))).1
  have hfc : xp1.tcbFaultHandler = absCap c := by rw [ha', hCR.abs]
  have hcv : capV (L.mem s1') (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3)) = c := capV_of_capAt hca
  have hcNE : c = .Null ∨ ∃ ep b0 b1 b2 b3 b4, c = .Endpoint ep b0 b1 b2 b3 b4 := by
    rw [← hcv]
    rcases hnoe with h | ⟨ep, b0, b1, b2, b3, b4, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨ep, b0, b1, b2, b3, b4, h⟩
  have hfcS : xp1.tcbFaultHandler = .nullCap ∨ ∃ e b R, xp1.tcbFaultHandler = .endpointCap e b R := by
    rw [hfc]
    rcases hcNE with h | ⟨ep, b0, b1, b2, b3, b4, h⟩
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr ⟨_, _, _, by rw [h]; rfl⟩
  -- the install
  rw [hrc]; simp only [bind_ok]; rw [tcs_fault_eq]
  have hxs : IsSlot Z.th x2 := by rw [hxe2]; exact AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
  have hc1 : capV (L.mem s1') x2 = capV (L.mem s) x2 := hS1.capV hxs
  have hnf := vfh_not_frame hv
  have hok : NewCapOK Z.th (L.mem s1') (capV (L.mem s) x2) e2.2 := by
    rw [← hc1, hxe2]; exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps hps1 (by rw [← hxe2, hc1]; exact hnf)
  have hI := install_fhOkJM arI (hHp.ins (L.ksb s1')) (hHp.del (L.ksb s1')) s1' s1' ar σ1' Z.G hDS1 hW1 p hp 3 (by simp [tcbSlots]) (by decide)
    layout.tcb.SLOT_FAULT_HANDLER (by simp [layout.tcb.SLOT_FAULT_HANDLER]) (InstFr.refl _ _ _) ssl hAs
    (capV (L.mem s) x2) e2.2 hok (fun _ => vfh_ep hv) hnoe
  rw [← hxe2] at hI
  obtain ⟨⟨r, s2, a1⟩, hins, ⟨σ2, G2, hc, hDS2⟩, hfr⟩ := spec_exists hI
  have he2 : e2 = (absCap (capV (L.mem s) x2), e2.2) := by rw [← he21]
  rw [hins]
  simp only [bind_ok, uncurry_apply_pair]
  rcases hc with ⟨hr, hx, -, hW2⟩ | ⟨hr, hx, hWp⟩
  swap
  · -- preempted: `JAtPre`
    simp only at hr; subst hr
    rw [← he2] at hx
    obtain ⟨⟨s0', a0', σ0', ⟨V0, Ac0, Lst0, D0, J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩, hPre⟩ := hWp
    refine (WP.spec_ok _).2 (Or.inr ⟨_, hdec, σ1', hst1, (.error (), σ2), ?_, ⟨Z.th, G2, Or.inr ⟨rfl, rfl⟩,
      J0.xtop.rel.1, hDS2.1, hDS2.2.2, hDom, hMO⟩, ?_⟩)
    · show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched p.bv ssl (some e2)
        (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ1').1
      simp only [Fl4Spec.invokeTcb]
      exact mem_bindE_err hx
    · show if _ = _ then _ else _
      rw [if_pos rfl]
      exact hPre
  simp only at hr; subst hr
  rw [← he2] at hx
  obtain ⟨V2, Ac2, Lst2, D2, J2, -, hns2, -, -⟩ := (hHp.ins _).wjr _ _ _ _ hW2
  -- the spec after the install
  have hpost2 := specPost_install hkp1 hfc hcNE hx hpost1
  obtain ⟨hCI, htm2, hid2, hscK, hstK⟩ := install_sched σ1' σ2 p.bv xp1 ssl e2 hkp1 hfcS J1.inv hx
  have hC2 : Sched.CurInv σ2 := hCI hC1
  have hct2 : σ2.curThread = σ1'.curThread := Vs.DK.ct (Vs.dke_installTcbCap' p.bv ssl 3 (some e2)) hx
  obtain ⟨x, hk2, -, -, -, hU2, hB2⟩ := hpost2
  -- the slots after the install: those holding neither the null cap nor an endpoint cap kept
  have hroot1 : ∀ y, IsSlot Z.th y → capV (L.mem s) y ≠ .Null →
      (∀ e b0 b1 b2 b3 b4, capV (L.mem s) y ≠ .Endpoint e b0 b1 b2 b3 b4) →
      capV (L.mem s2) y = capV (L.mem s) y := fun y hy hn he => by
    have hne : y ≠ cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3) := fun e => by
      rw [← hS1.capV hy, e] at hn he
      rcases hnoe with h | ⟨ep, b0, b1, b2, b3, b4, h, -⟩
      · exact hn h
      · exact he _ _ _ _ _ _ h
    rw [hfr rfl y hy hne, hS1.capV hy]
  -- `set_mcp`
  unfold schedTail
  rw [set_mcp_eq, bind_ok]
  obtain ⟨V3, J3⟩ := J2.mcpWrJ hpT hk2 y0 (Fl4Spec.ucast 8 y0.bv)
    (by rw [Ipc.ucast8_specPrio, Sched.specPrio_toNat hy0])
  set σa := Notif.updK σ2 p.bv (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 y0.bv }) with hσa
  have hSS3 := J2.mcp_slots hpT y0
  have ha : ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 y0.bv) σ2).1 := by
    show _ ∈ (Fl4Spec.threadSet (Z := Unit) _ p.bv σ2).1
    rw [Notif.threadSet_eq _ hk2]; exact Set.mem_singleton _
  have hCa : Sched.CurInv σa := (QKM.mcp hk2 _).curInv hC2
  have hneA : σa.curThread ≠ σa.idleThread := by
    show σ2.curThread ≠ σ2.idleThread
    rw [hct2, hid2, hct1, hid1]; exact hni.1
  obtain ⟨hc3, hp3⟩ := J3.prioCur hneA hCa hpT
  -- `set_priority`
  refine WP.spec_bind (J3.setPrioJS (fun u => hns2 u) hpT y1 hy1 hc3 hp3) ?_
  rintro s4 ⟨σb, hmb, hPF, hSS4, V4, J4⟩
  have hb : ((), σb) ∈ (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 y1.bv) σa).1 := by
    rw [hmb]; exact Set.mem_singleton _
  have hCb : Sched.CurInv σb := hPF.curInv hCa
  have hnsb : ∀ u, σb.schedulerAction ≠ .switchThread u := fun u e => by
    rcases hPF.act with e' | e' <;> rw [e'] at e
    · exact hns2 u e
    · cases e
  have hvk : VK σ2 σb := (presV_setMcpriority _ _ σ2 _ ha).trans (presV_setPriority _ _ σa _ hb)
  obtain ⟨xb, hkb, hstb, hscb⟩ := hvk.tcb _ x hk2
  have hidb : p.bv ≠ σb.idleThread := by
    rw [hPF.sk.idle]
    show p.bv ≠ σ2.idleThread
    rw [hid2, hid1]
    obtain ⟨Q0, R0, hc0, hs0⟩ := J.xtop.fin.1.1.1.lists
    have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
      unfold P1.LawfulStore.idleW nodeW; rw [hc0.cur]
    intro e
    exact hpI (Eq.symm (by rw [ei]; apply P1.eq_of_bv; rw [← hs0.idleTh, ← e]))
  -- the outcome
  have fin : ∀ (s5 : S) (a5 : A) (σc : Fl4Spec.State Unit), ((), σc) ∈ (scStep p.bv sco σb).1 →
      (∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s5 a5 σc) →
      (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a5) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
        TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) σ blk call don m s res ⦄ := by
    rintro s5 a5 σc hcc ⟨Z', Ac', Lst', D', J'⟩
    rw [WP.spec_ok]
    refine TopPostDMX.toPne (Or.inr ⟨_, hdec, σ1', hst1, (.ok [], σc), ?_, ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩,
      J'.xtop.rel.1, J'.xtop.rel.2.1, J'.xtop.rel.2.2.1, J'.xtop.rel.2.2.2.1, J'.xtop.rel.2.2.2.2.1⟩,
      ⟨Z', H, Cs, Ac', Lst', D', J'⟩⟩) (by simp)
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched p.bv ssl (some e2)
      (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ1').1
    simp only [Fl4Spec.invokeTcb]
    exact mem_bindE_ok hx (mem_bindE_ok (mem_liftE ha) (mem_bindE_ok (mem_liftE hb)
      (mem_bindE_ok (mem_liftE hcc) (Set.mem_singleton _))))
  cases scf
  · -- no SC step
    have hsco : sco = none := h1.2 rfl
    subst hsco
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact fin s4 a1 σb (Set.mem_singleton _) ⟨_, _, _, _, J4⟩
  simp only [↓reduceIte]
  step with Sched.obj.Sc.is_null.spec' as ⟨bz, hbz⟩
  by_cases hs0 : scv = 0#u64
  · -- the unbind
    have hsco : sco = some none := by
      cases sco with
      | none => exact absurd (h1.1 rfl) (by simp)
      | some o =>
        cases o with
        | none => rfl
        | some v => exact absurd hs0 (h3 v rfl).2
    subst hsco
    rw [hbz, decide_eq_true hs0]
    simp only [↓reduceIte]
    obtain ⟨cc, y, n, hcx, hks, hy⟩ := hU2 rfl
    have hksb : σb.kheap cc = some (.schedContext y n) := (hvk.sc cc y n).2 hks
    have hxbsc : xb.tcbSchedContext = some cc := by rw [hscb, hcx]
    obtain ⟨Qb, Rb, hcb, hsbl⟩ := J4.xtop.fin.1.1.1.lists
    obtain ⟨xb', hkb', -, -, hscw, -⟩ := hsbl.tcb p hpT
    rw [hkb] at hkb'; cases hkb'
    step with P1.obj.Tcb.sc.spec as ⟨i4, hi4⟩
    have hi40 : i4 ≠ 0#u64 := fun e => by rw [hscw, ← hi4, e, Notif.optRef_zero] at hxbsc; cases hxbsc
    have hi4c : i4.bv = cc := by rw [hscw, ← hi4, Notif.optRef_ne hi40] at hxbsc; exact Option.some.inj hxbsc
    have hi4C : i4 ∈ Z.C := by rw [hi4]; exact hsbl.scMem p hpT (by rw [← hi4]; exact hi40)
    step with Sched.obj.Sc.is_null.spec' as ⟨b1, hb1⟩
    rw [hb1, decide_eq_false hi40]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (J4.unbindTcbJ hpT hi4C hkb (by rw [hxbsc, hi4c]) (fun u e => absurd e (hnsb u)) hidb) ?_
    rintro s5 ⟨σc, hsc, Ac5, Lst5, D5, J5⟩
    refine fin s5 a1 σc ?_ ⟨_, Ac5, Lst5, D5, J5⟩
    show _ ∈ ((Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext p.bv >>= fun o =>
      Fl4Spec.NonDet.assertOpt o >>= fun c => Fl4Spec.schedContextUnbindTcb c) σb).1
    rw [nd_bind_one (Endp.getTcbObjRef_eq _ hkb), hxbsc]
    rw [nd_bind_one (show (Fl4Spec.NonDet.assertOpt (some cc) : Fl4Spec.SMonad Unit Fl4Spec.ObjRef) σb =
      ({(cc, σb)}, False) from rfl), ← hi4c, hsc]
    exact Set.mem_singleton _
  · -- the bind
    have hsco : sco = some (some scv.bv) := by
      cases sco with
      | none => exact absurd (h1.1 rfl) (by simp)
      | some o =>
        cases o with
        | none => exact absurd (h2 rfl) hs0
        | some v => rw [(h3 v rfl).1]
    subst hsco
    rw [hbz, decide_eq_false hs0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨-, yd, nd, hkd, hyd0, hreld⟩ := hDB _ rfl
    obtain ⟨x0, -, -, hkt0', hxs0', -⟩ := hB2 _ rfl
    rw [hk2] at hkt0'; cases hkt0'
    have hxb0 : xb.tcbSchedContext = none := by rw [hscb]; exact hxs0'
    -- the SC and the release check, carried from the decode
    have hdc : scv.bv ≠ ct.bv := fun e => by rw [e, hkc] at hkd; cases hkd
    have hk1d : σ1'.kheap scv.bv = some (.schedContext yd nd) := by
      rw [restart_kheap hkc hst1c, Function.update_of_ne hdc]; exact hkd
    have hkbd : σb.kheap scv.bv = some (.schedContext yd nd) := (hvk.sc _ yd nd).2 (hscK _ yd nd hk1d hyd0)
    have hpct : p.bv ≠ ct.bv := fun e => hpc _ rfl (by rw [e, hcur])
    have hkp1' : σ1'.kheap p.bv = some (.tcb xp) := by
      rw [restart_kheap hkc hst1c, Function.update_of_ne hpct]; exact hkp
    rw [hkp1'] at hkp1; cases hkp1
    have hrelb : Fl4Spec.ipcQueuedThreadState xb.tcbState = true → Fl4Spec.scReleased σb.curTime yd = true := by
      intro hq
      rw [hstb] at hq
      have e := hstK x hk2 hq
      rw [hvk.tm, htm2, htm1]
      exact hreld (by rw [← e]; exact hq)
    -- the pair's caps, kept by the steps
    have hTn : capV (L.mem s) (cslotAddr ssl) ≠ .Null := by rw [hpsl]; exact fun h => by cases h
    have hTe : ∀ e b0 b1 b2 b3 b4, capV (L.mem s) (cslotAddr ssl) ≠ .Endpoint e b0 b1 b2 b3 b4 := by
      intro e b0 b1 b2 b3 b4 h; rw [hpsl] at h; cases h
    have hT4 : capAt (L.mem s4) (cslotAddr ssl) = ok (.Thread p) := by
      rw [capAt_capV, hSS4.capV hAs.isSlot, hSS3.capV hAs.isSlot, hroot1 _ hAs.isSlot hTn hTe, hpsl]
    obtain ⟨xs, sb, hxsS, hxsc⟩ := hscs hs0
    have hSn : capV (L.mem s) xs ≠ .Null := by rw [hxsc]; exact fun h => by cases h
    have hSe : ∀ e b0 b1 b2 b3 b4, capV (L.mem s) xs ≠ .Endpoint e b0 b1 b2 b3 b4 := by
      intro e b0 b1 b2 b3 b4 h; rw [hxsc] at h; cases h
    have hS4 : capAt (L.mem s4) xs = ok (.SchedContext scv sb) := by
      rw [capAt_capV, hSS4.capV hxsS, hSS3.capV hxsS, hroot1 _ hxsS hSn hSe, hxsc]
    obtain ⟨hscvC, -, hsb, hssz, -⟩ := J4.scCtxCap arI hxsS hS4
    refine WP.spec_bind (J4.bindTcbJ hAT hAK hTA hscvC hpT hkbd hyd0 hkb hxb0 hrelb hnsb hCb hidb
      hAs.isSlot hT4 hxsS hS4 hsb (hssz yd nd hkbd)) ?_
    rintro ⟨s5, a5⟩ ⟨σc, hsc, Ac5, Lst5, D5, J5⟩
    try simp only [uncurry_apply_pair]
    refine fin s5 a5 σc ?_ ⟨_, Ac5, Lst5, D5, J5⟩
    show _ ∈ (Fl4Spec.schedContextBindTcb (Z := Unit) scv.bv p.bv σb).1
    rw [hsc]; exact Set.mem_singleton _

set_option maxHeartbeats 8000000 in
/-- **The SetSchedParams label at `JAt`** (`JAtPre` if preempted; as
XTopTcbSched's `tcb_set_sched_paramsX`): the decode (the authority's MCP by
`JAtZ`'s `McpRel`, the SC checks by the scheduler and notification
relations), then `ssp_tailJM`. -/
theorem tcb_set_sched_paramsJM [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz) (hRs : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (hAT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSchedParams)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hpI : p ≠ L.idleW s)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (hpsl : capV (L.mem s) (cslotAddr ssl) = .Thread p)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ fl4_abi.label.TCBSetSchedParams p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hS : SchedRel st Z.N Z.T Z.C Z.c s σ := J.xtop.fin.1.1.1
  have hR : Notif.NtfnStateRel Z.N Z.T (L.mem s) σ := J.xtop.fin.1.1.2.2.1
  have hpT : p ∈ Z.T := J.thT p hp
  have hM := J.mcp
  have hC0 := J.c0
  have hcur : σ.curThread = ct.bv := (J.curEq hct).1
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetSchedParams (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKXP
  rw [decode_ssp_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 2 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSchedParams (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetSchedParams
    by_cases ha : args.length < 2
    · rw [whenE_pos (by simpa using ha)]
      exact run_throw_bind _ _ _
    · rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (h.resolve_left ha)]
      exact run_throw_bind _ _ _
  unfold tcb.decode_set_sched_params tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 2#u64 ↔ 2 ≤ args.length := by
    show length >= 2#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 2 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hXc.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hXc.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hl with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
  have ha0 := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  have ha1 := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 1#u64 y1 (by simp))
  simp only [ha0, ha1, bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hXc.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hXc.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hXc.get hx2' h2
  have hexl : ¬ excaps.length < 3 := by
    have := (List.getElem?_eq_some_iff.1 he2).1; omega
  -- the spec up to the authority's cap
  have hspec0 : (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ = ((match e0.1 with
        | .threadCap tcbPtr => Fl4Spec.NonDetE.returnOk tcbPtr
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.checkPrio (Z := Unit) y0.bv q >>= fun _ => Fl4Spec.checkPrio (Z := Unit) y1.bv q >>= fun _ =>
        Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1 >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ := by
    unfold Fl4Spec.decodeSetSchedParams
    rw [whenE_neg (by simp), retOk_bind, whenE_neg hexl, retOk_bind, retOk_bind, retOk_bind, retOk_bind,
      retOk_bind, retOk_bind, he0, he1, he2, the_some, the_some, the_some]
    generalize e0.1 = cc
    cases cc <;> rfl
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  swap
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec0, he01]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_throw_bind _ _ _
  obtain ⟨q, hq⟩ := hth
  rw [thread_arg_thread s 1#u64 hq]
  simp only [bind_ok, check_prio_eq]
  have hqT := hcapT h0 q hq
  have he0' : e0.1 = .threadCap q.bv := by rw [he01, hq]; rfl
  rw [he0'] at hspec0
  simp only [] at hspec0
  rw [retOk_bind] at hspec0
  have hcp0 := checkPrio_run hM hqT y0.bv
  have hcp1 := checkPrio_run hM hqT y1.bv
  obtain ⟨xq, hkq, hmq⟩ := hM q hqT
  have hmq8 : (L.mem s (mcpA q)).val < 256 := by rw [hmq]; exact xq.tcbMcpriority.isLt
  by_cases hg0 : y0 > L.mem s (mcpA q)
  · rw [ite_eq_left hg0]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec0, runE_bind_congr hcp0, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hg0)]
    exact run_throw_bind _ _ _
  rw [ite_eq_right hg0]
  simp only [bind_ok]
  by_cases hg1 : y1 > L.mem s (mcpA q)
  · rw [ite_eq_left hg1]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec0, runE_bind_congr hcp0, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg0), retOk_bind,
      runE_bind_congr hcp1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hg1)]
    exact run_throw_bind _ _ _
  rw [ite_eq_right hg1]
  simp only [bind_ok]
  have hy0 : y0.val < 256 := by have : ¬ (L.mem s (mcpA q)).val < y0.val := hg0; omega
  have hy1 : y1.val < 256 := by have : ¬ (L.mem s (mcpA q)).val < y1.val := hg1; omega
  have hspec1 : (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ = (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1 >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)).run σ := by
    rw [hspec0, runE_bind_congr hcp0, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg0), retOk_bind,
      runE_bind_congr hcp1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg1), retOk_bind]
  obtain ⟨Q, R', hcL, hsL⟩ := hS.lists
  obtain ⟨xp, hkp, -, -, hxts, -⟩ := hsL.tcb p hpT
  have hsc0 : obj.Tcb.sc st p s = ok (L.mem s (P1.scA p)) := by
    obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Tcb.sc.spec (L := L) s p); exact hw
  -- after the SC check: the fault handler, the restart and the invocation
  have hafter : ∀ (scv : U64) (sco : Option (Option Fl4Spec.ObjRef)),
      (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1).run σ = ({(.ok sco, σ)}, False) →
      (sco = none ↔ (L.mem s (P1.scA p) != scv) = false) → (sco = some none → scv = 0#u64) →
      (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) → ScDec σ p.bv sco →
      (scv ≠ 0#u64 → ∃ xs sb, IsSlot Z.th xs ∧ capV (L.mem s) xs = .SchedContext scv sb) →
      (do
        let i ← lift (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO)
        let flags ← lift (i ||| tcb.SCHED_UPDATE_FAULT)
        if (L.mem s (P1.scA p) != scv) = true then do
            let flags1 ← lift (flags ||| tcb.SCHED_UPDATE_SC)
            let fh ← obj.Slot.cap st x2 s
            let b ← faults.valid_fault_handler fh
            if b = true then do
                let s1 ← tcb.restart_caller st s
                tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (fh, x2) y0 y1 scv flags1
              else do
                let r7 ← error.invalid_cap Unit 3#u64
                ok (r7, s, ar)
          else do
            let fh ← obj.Slot.cap st x2 s
            let b ← faults.valid_fault_handler fh
            if b = true then do
                let s1 ← tcb.restart_caller st s
                tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (fh, x2) y0 y1 scv flags
              else do
                let r7 ← error.invalid_cap Unit 3#u64
                ok (r7, s, ar)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
    intro scv sco hdus hs1 hs2 hs3 hD hscs
    simp only [lift, bind_ok, slot_cap_eq, capAt_capV, vfh_eq]
    by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x2))
    · simp only [decide_eq_true hv, ↓reduceIte]
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (.threadControlSched p.bv ssl (some e2)
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, run_bind_ok_st hdus]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he21]; exact hv)]
        show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e2) >>= _).run σ = _
        rw [retOk_bind, retOk_bind]; rfl
      by_cases hscf : (L.mem s (P1.scA p) != scv) = true
      · simp only [hscf, ↓reduceIte]
        have h1' : sco = none ↔ true = false := by rw [hs1, hscf]
        have := ssp_tailJM arI s ar σ J hni hsg hP0 hHp hRs hAT hAK hTA p hp ct hct ssl hAs hpsl x2 e2 hxe2 he21 ps2
          hps2 hps21 hv y0 y1 scv hy0 hy1 true q.bv sco h1' hs2 hs3 hD hpI hscs _ (DecOut.of_eq hdec) blk call don
        simp only [↓reduceIte] at this
        exact this
      · simp only [Bool.not_eq_true] at hscf
        simp only [hscf, Bool.false_eq_true, ↓reduceIte]
        have h1' : sco = none ↔ false = false := by rw [hs1, hscf]
        have := ssp_tailJM arI s ar σ J hni hsg hP0 hHp hRs hAT hAK hTA p hp ct hct ssl hAs hpsl x2 e2 hxe2 he21 ps2
          hps2 hps21 hv y0 y1 scv hy0 hy1 false q.bv sco h1' hs2 hs3 hD hpI hscs _ (DecOut.of_eq hdec) blk call don
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        exact this
    · simp only [decide_eq_false hv, Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
      have hiv : ∀ (scf : Bool), (ok ((.Err (.Sys (.InvalidCapability 3#u64)) : core.result.Result Unit error.Exc), s, ar) :
          Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
        intro _
        refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 3, ?_, Or.inr ⟨3#u64, rfl, rfl⟩⟩, hJ0⟩)
        apply run_liftME_err
        rw [hspec1, run_bind_ok_st hdus]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he21]; exact hv)]
        exact run_bind_error (run_throw_bind _ _ _) _
      split <;> exact hiv true
  have hpre : ∀ cp : Fl4Spec.Cap, e1.1 = cp →
      (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl cp >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)).run σ := by
    rintro cp rfl; exact hspec1
  unfold tcb.sched_params_sc
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases hc1 : capV (L.mem s) x1
  case Null =>
    rw [he11, hc1] at hspec1
    simp only [absCap] at hspec1
    rw [hct]
    simp only [bind_ok, obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
    by_cases hpc : p = ct
    · simp only [decide_eq_true hpc, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec1]
      refine run_bind_error ?_ _
      rw [dus_null hkp ssl, whenE_pos (by rw [hcur, hpc])]
      exact run_throw_bind _ _ _
    · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte, bind_ok, hsc0]
      have hpc' : ¬ p.bv = σ.curThread := by rw [hcur]; intro e; exact hpc (P1.eq_of_bv e)
      refine hafter 0#u64 _ (by rw [he11, hc1]; simp only [absCap]; rw [dus_null hkp ssl, whenE_neg hpc', retOk_bind]; rfl)
        ?_ (fun _ => rfl) (fun v h => by split at h <;> cases h)
        ⟨xp, hkp, fun h => ⟨hpc', fun e => (by simp [e] at h)⟩, fun v h => (by split at h <;> cases h)⟩ (fun h => absurd rfl h)
      rw [hxts]
      by_cases hz : L.mem s (P1.scA p) = 0#u64
      · simp [hz, Notif.optRef_zero]
      · simp [hz, Notif.optRef_ne hz]
  case SchedContext ptr sz =>
    have hx1S : IsSlot Z.th x1 := by rw [hxe1]; exact AbsSlot.isSlot ⟨ps1, hps11, Or.inl hps1⟩
    have hscsP : ptr ≠ 0#u64 → ∃ xs sb, IsSlot Z.th xs ∧ capV (L.mem s) xs = .SchedContext ptr sb :=
      fun _ => ⟨x1, sz, hx1S, hc1⟩
    rw [he11, hc1] at hspec1
    simp only [absCap] at hspec1
    have hpC := hcapC h1 ptr sz hc1
    have hptr0 := hC0 ptr hpC
    obtain ⟨y, n, hks, hx⟩ := hsL.scs ptr hpC
    have hne : Fl4Spec.scActive y = true → y.scRefills ≠ [] := fun ha => by
      rw [(hx.strong ha).refills]; exact refills_ne (hx.strong ha).wf
    have hdus := dus_sc hkp hks hne ssl (sz.val - Fl4Spec.minSchedContextBits)
    have hst := (hR.at_tcb hpT hkp).st
    have hxt' : y.scTcb = Notif.optRef (L.mem s (scW ptr 24#u64)) := hx.tcb
    have hcons : (((if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = none ↔
          (L.mem s (P1.scA p) != ptr) = false) ∧
        ((if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = some none → ptr = 0#u64) ∧
        (∀ v, (if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = some (some v) →
          v = ptr.bv ∧ ptr ≠ 0#u64)) := by
      rw [hxts]
      refine ⟨?_, (fun h => by split at h <;> cases h), (fun v h => by split at h <;> cases h; exact ⟨rfl, hptr0⟩)⟩
      simp only [ne_eq, bv_optRef_some hptr0]
      by_cases e : L.mem s (P1.scA p) = ptr <;> simp [e]
    have hillT : (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl
          (.schedContextCap ptr.bv (sz.val - Fl4Spec.minSchedContextBits))).run σ =
          ({(.error .illegalOperation, σ)}, False) →
        (ok ((.Err (.Sys .IllegalOperation) : core.result.Result Unit error.Exc), s, ar) :
          Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
      intro h
      refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec1]
      exact run_bind_error h _
    simp only [hsc0, bind_ok]
    by_cases hip : L.mem s (P1.scA p) = ptr
    · -- the thread's own SC
      have hc1' : ¬ (xp.tcbSchedContext ≠ some ptr.bv ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none)) := by
        rw [hxts, hip, Notif.optRef_ne hptr0]; simp
      rw [if_neg (show ¬ (L.mem s (P1.scA p) != ptr) = true by simp [hip])]
      obtain ⟨bb, hbb, rfl⟩ := spec_exists (is_blocked_spec s p xp.tcbState hst)
      rw [hbb]; simp only [bind_ok]
      by_cases hb : Fl4Spec.ipcQueuedThreadState xp.tcbState = true
      · simp only [hb, ↓reduceIte]
        obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sc_released_refines s σ hS hpC hks)
        rw [hb1e]; simp only [bind_ok]
        rw [getScReleased_eq hks hne] at hb1
        have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
        by_cases hr : b1 = true
        · simp only [hr, ↓reduceIte, bind_ok]
          refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
            ⟨xp, hkp, fun h => (by split at h <;> cases h),
              fun v h => (by rw [if_neg (by rw [hxts, hip, Notif.optRef_ne hptr0]; simp)] at h; cases h)⟩ hscsP
          rw [he11, hc1]; simp only [absCap]
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by rw [eb, hr]; simp), retOk_bind]; rfl
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine hillT ?_
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_pos ⟨hb, by rw [eb]; simpa using hr⟩
]
          exact run_throw_bind _ _ _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
          ⟨xp, hkp, fun h => (by split at h <;> cases h),
              fun v h => (by rw [if_neg (by rw [hxts, hip, Notif.optRef_ne hptr0]; simp)] at h; cases h)⟩ hscsP
        rw [he11, hc1]; simp only [absCap]
        rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by simp [hb]), retOk_bind]; rfl

    · have hne1 : (L.mem s (P1.scA p) != ptr) = true := by simp [hip]
      simp only [hne1, ↓reduceIte]
      by_cases hi0 : L.mem s (P1.scA p) = 0#u64
      swap
      · have : (L.mem s (P1.scA p) != 0#u64) = true := by simp [hi0]
        simp only [this, ↓reduceIte, error.illegal, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine hillT ?_
        rw [hdus, whenE_pos ⟨by rw [hxts, Ne, bv_optRef_some hptr0]; exact hip,
          Or.inl (by rw [hxts, Notif.optRef_ne hi0]; simp)⟩]
        exact run_throw_bind _ _ _
      have : (L.mem s (P1.scA p) != 0#u64) = false := by simp [hi0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hscT : obj.Sc.tcb st ptr s = ok (L.mem s (scW ptr 24#u64)) := by
        obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Sc.tcb.spec (L := L) s ptr); rw [scTcbA_eq] at hw; exact hw
      simp only [hscT, bind_ok]
      have hx0n : xp.tcbSchedContext = none := by rw [hxts, hi0, Notif.optRef_zero]
      by_cases ht0 : L.mem s (scW ptr 24#u64) = 0#u64
      swap
      · have : (L.mem s (scW ptr 24#u64) != 0#u64) = true := by simp [ht0]
        simp only [this, ↓reduceIte, error.illegal, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine hillT ?_
        rw [hdus, whenE_pos ⟨by rw [hx0n]; simp, Or.inr (by rw [hxt', Notif.optRef_ne ht0]; simp)⟩]
        exact run_throw_bind _ _ _
      have : (L.mem s (scW ptr 24#u64) != 0#u64) = false := by simp [ht0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hc1' : ¬ (xp.tcbSchedContext ≠ some ptr.bv ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none)) := by
        rw [hx0n, hxt', ht0, Notif.optRef_zero]; simp
      obtain ⟨bb, hbb, rfl⟩ := spec_exists (is_blocked_spec s p xp.tcbState hst)
      rw [hbb]; simp only [bind_ok]
      by_cases hb : Fl4Spec.ipcQueuedThreadState xp.tcbState = true
      · simp only [hb, ↓reduceIte]
        obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sc_released_refines s σ hS hpC hks)
        rw [hb1e]; simp only [bind_ok]
        rw [getScReleased_eq hks hne] at hb1
        have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
        by_cases hr : b1 = true
        · simp only [hr, ↓reduceIte, bind_ok]
          refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
            ⟨xp, hkp, fun h => (by split at h <;> cases h), fun v h => ⟨hx0n, (by
              have hv : v = ptr.bv := (by split at h <;> cases h; rfl)
              subst hv
              exact ⟨y, n, hks, (by rw [hxt', ht0, Notif.optRef_zero]), (fun _ => by rw [← hr, eb])⟩)⟩⟩ hscsP
          rw [he11, hc1]; simp only [absCap]
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by rw [eb, hr]; simp), retOk_bind]; rfl
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine hillT ?_
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_pos ⟨hb, by rw [eb]; simpa using hr⟩
]
          exact run_throw_bind _ _ _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
          ⟨xp, hkp, fun h => (by split at h <;> cases h), fun v h => ⟨hx0n, (by
              have hv : v = ptr.bv := (by split at h <;> cases h; rfl)
              subst hv
              exact ⟨y, n, hks, (by rw [hxt', ht0, Notif.optRef_zero]), (fun hq => absurd hq hb)⟩)⟩⟩ hscsP
        rw [he11, hc1]; simp only [absCap]
        rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by simp [hb]), retOk_bind]; rfl

  all_goals
    rw [he11, hc1] at hspec1
    simp only [error.invalid_cap, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 2, ?_, Or.inr ⟨2#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec1]
    exact run_bind_error (dus_other hkp ssl (by simp [absCap]) (by simp [absCap])) _


end

end

end Fl4Proofs.P3
