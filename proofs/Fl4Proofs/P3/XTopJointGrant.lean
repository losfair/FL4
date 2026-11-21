/-
P3 (DESIGN.md §9), IPC: **a granted transfer's caps at `J`** (toward
XTopJointIpcJ's `JReplyRestHyp` and `JSendRestHyp`): FL4's `transfer_caps`
from `JAtZ` before to `JAtZ` after, against the spec's `transfer_caps`.

* `JAtZ.insDJ`: `cdt::insert` of a derived cap from a CNode slot into an
  empty CNode slot at `J` (the CNode copy's step, CnodeCopy's
  `decode_copy_rel` insert case: `insert_full_finG`, `insert_trace`,
  `insert_delinv_imp`, `typedKept_ins`, `utSrc_ins`, `coverUt_ins`; then
  `XTopAt.slotStep` and XTopJointRest's `jowes_cn`, both slots' CNodes live,
  `DestLive`).
-/
import Fl4Proofs.P3.XTopJointFault
import Fl4Proofs.P3.XTopJointRest
import Fl4Proofs.P3.IpcGrantX
import Fl4Proofs.P3.CnUtSrc
import Fl4Proofs.P3.SlotCover
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- A TCB's slot is no CNode slot. -/
theorem slotOf_ne_cn {th : TypedHeap} (hP : Placed th) {t : U64} {n : Nat} (hn : IsSlotAt th t n)
    (ht : th t = some .tcb) {q : U64} {r : Nat} {idx : List Bool} (hq : th q = some (.cnode r))
    (hl : idx.length = r) : slotOf t n ≠ cslotAddr (q.bv, idx) := by
  intro e
  obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := th) (sl := (q.bv, idx)) ⟨q, rfl, Or.inl (by rw [hl]; exact hq)⟩
  have hpp : p = q := P1.eq_of_bv hp1.symm
  subst hpp
  have := IsSlotAt.apart hP hn hi (fun hh => by obtain ⟨h, -⟩ := hh; subst h; rw [hq] at ht; cases ht)
  rw [e, hp2] at this; omega


/-! ## The slots' CNodes live -/

section Live
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`lookup_cap`'s cap is held in a slot** (the slot the walk ends at). -/
theorem lookup_cap_held (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (t : U64) (ht : th t = some .tcb)
    (cptr : U64) :
    cspace.lookup_cap st s t cptr ⦃ r => ∀ c, r = .Ok c → ∃ y, IsSlot th y ∧ capV (L.mem s) y = c ⦄ := by
  unfold cspace.lookup_cap
  refine WP.spec_bind (lookup_slot_refines th s σ hR hV t ht cptr) ?_
  rintro r ⟨e, -, hrel, hok⟩
  cases r with
  | Ok r1 =>
    cases e with
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth, -⟩ := hok
      obtain ⟨c, a, hc, -, -⟩ := hR.slot_cap (Z := Unit) hp hth
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, WP.spec_ok]
      rintro c' h
      cases h
      exact ⟨_, (AbsSlot.isSlot ⟨p, hp, Or.inl hth⟩ : IsSlot th (cslotAddr sl)), capV_of_capAt hc⟩
    | error _ => exact hrel.elim
  | Err lf =>
    simp only [WP.spec_ok]
    intro c h; cases h

set_option maxHeartbeats 4000000 in
/-- **`get_receive_slot`'s slot lies in a live CNode** (`DestLive`: reached
by `lookup_target_slot` from a root cap held in a slot, `DestCap.of_cnRef`). -/
theorem get_receive_slot_live (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) (rbw : U64) :
    ipc.get_receive_slot st s t rbw ⦃ dest => dest ≠ 0#u64 → ∃ pd idx, dest = cslotAddr (pd.bv, idx) ∧
      th pd = some (.cnode idx.length) ∧ DestCap th (L.mem s) pd ⦄ := by
  unfold ipc.get_receive_slot
  by_cases hr0 : rbw = 0#u64
  · rw [if_pos hr0, WP.spec_ok]; intro h; exact absurd rfl h
  rw [if_neg hr0, Ipc.buf_recv_eq.1, Ipc.buf_recv_eq.2.1, Ipc.buf_recv_eq.2.2]
  simp only [bind_ok]
  refine WP.spec_bind (msg.buf_get.spec s rbw _) ?_
  rintro root -
  refine WP.spec_bind (msg.buf_get.spec s rbw _) ?_
  rintro index -
  refine WP.spec_bind (msg.buf_get.spec s rbw _) ?_
  rintro depth -
  refine WP.spec_bind (WP.spec_and (Ipc.lookup_cap_valid th s σ hR hV t ht root)
    (lookup_cap_held th s σ hR hV t ht root)) ?_
  rintro r ⟨⟨⟨e, -, hrel⟩, hval⟩, hheld⟩
  cases r with
  | Err lf => simp only [WP.spec_ok]; intro h; exact absurd rfl h
  | Ok c0 =>
    cases e with
    | error _ => simp [CapResRel] at hrel
    | ok a =>
      have hcv := hval c0 rfl
      simp only []
      unfold cspace.lookup_target_slot
      refine WP.spec_bind (lookup_slot_for_cnode_op_refines th s σ hR hV false c0 a hrel hcv index depth) ?_
      rintro r1 ⟨e1, -, hrel1⟩
      cases r1 with
      | Err _ => simp only [WP.spec_ok]; intro h; exact absurd rfl h
      | Ok slot =>
        cases e1 with
        | error _ => exact hrel1.elim
        | ok sl =>
          obtain ⟨hsl, p, hp1, hp, hcr⟩ := hrel1
          obtain ⟨c1, hc1⟩ := capAt_total (L.mem s) slot
          simp only []
          rw [slot_cap_eq, hc1]
          simp only [bind_ok]
          have hlive : ∃ pd idx, slot = cslotAddr (pd.bv, idx) ∧ th pd = some (.cnode idx.length) ∧
              DestCap th (L.mem s) pd :=
            ⟨p, sl.2, by rw [hsl, ← hp1], hp, DestCap.of_cnRef hcr (hheld c0 rfl)⟩
          by_cases hn : c1 = .Null
          · subst hn
            rw [cap_is_null_null, bind_ok, if_pos rfl, WP.spec_ok]
            exact fun _ => hlive
          · rw [cap_is_null_ne hn, bind_ok, if_neg Bool.false_ne_true, WP.spec_ok]
            intro h; exact absurd rfl h

/-- The extra-cap array's slots lie in live CNodes. -/
def ExtraLive (th : TypedHeap) (m : U64 → U64) (_kb : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  ∀ j, j < 3 → Ipc.exAt extra j ≠ 0#u64 → ∃ ps idx, Ipc.exAt extra j = cslotAddr (ps.bv, idx) ∧
    th ps = some (.cnode idx.length) ∧ DestCap th m ps

set_option maxHeartbeats 4000000 in
/-- **`lookup_extra_caps`' slots lie in live CNodes** (each reached by
`lookup_slot` from the thread's CSpace root, held in its TCB slot 0:
`DestCap.of_cnRef`). -/
theorem lookup_extra_live (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) (sbw : U64)
    (info : msginfo.MessageInfo) :
    ipc.lookup_extra_caps st s t sbw info ⦃ r => ∀ e, r = .Ok e → ExtraLive th (L.mem s) (L.ksb s) e ⦄ := by
  have hroot : ∃ y, IsSlot th y ∧ capV (L.mem s) y = capOf (L.mem s) (slotAddr t.bv 0#64) :=
    ⟨slotAddr t.bv 0#64, ⟨t, 0, Or.inr ⟨ht, by decide⟩, rfl⟩, (capOf_eq (capAt_capV _ _)).symm⟩
  unfold ipc.lookup_extra_caps
  by_cases h0 : sbw = 0#u64
  · rw [if_pos h0, WP.spec_ok]
    rintro e h j hj hne
    cases h
    exact absurd (Ipc.exAt_none j hj) hne
  rw [if_neg h0]
  unfold ipc.lookup_extra_caps_loop
  refine loop.spec_decr_nat (fun x => 3 - x.2.val)
    (fun x => x.2.val ≤ 3 ∧ ExtraLive th (L.mem s) (L.ksb s) x.1) _ _ _ (fun x hx => ?_) ?_
  · obtain ⟨arr, i⟩ := x
    obtain ⟨hi, hP⟩ := hx
    dsimp only at hi hP ⊢
    unfold ipc.lookup_extra_caps_loop.body
    by_cases hin : i < info.extra_caps
    · rw [if_pos hin]
      by_cases hi3 : i < 3#u64
      · have hi3' : i.val < 3 := by scalar_tac
        rw [if_pos hi3, Ipc.buf_caps_eq]
        simp only [lift, bind_ok]
        refine WP.spec_bind (msg.buf_get.spec s sbw _) ?_
        rintro w -
        refine WP.spec_bind (lookup_slot_refines th s σ hR hV t ht _) ?_
        rintro r ⟨e, -, hrel, hsok⟩
        cases r with
        | Ok r1 =>
          cases e with
          | error _ => exact hrel.elim
          | ok v =>
            obtain ⟨sl, rest⟩ := v
            obtain ⟨hsl, -⟩ := hrel
            obtain ⟨p, hp1, hp, hcr⟩ := hsok
            simp only []
            obtain ⟨a', ha', ha'v⟩ := spec_exists (Aeneas.Std.Array.update_spec arr (UScalar.cast .Usize i) r1.slot
              (by have hl : arr.val.length = 3 := by simpa using arr.property
                  rw [Ipc.cast_us_val i hi3']; simp [Aeneas.Std.Array.length, hl]; omega))
            rw [ha']
            simp only [bind_ok]
            obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
            rw [h4e, bind_ok, WP.spec_ok]
            have hi4 : i4.val = i.val + 1 := by simpa using h4v
            subst ha'v
            refine ⟨⟨show i4.val ≤ 3 by omega, fun j hj hne => ?_⟩, show 3 - i4.val < 3 - i.val by omega⟩
            try dsimp only at hne ⊢
            rw [Ipc.exAt_set, Ipc.cast_us_val i hi3'] at hne ⊢
            by_cases hji : i.val = j ∧ j < 3
            · rw [if_pos hji]
              exact ⟨p, sl.2, by rw [hsl, ← hp1], hp, DestCap.of_cnRef hcr hroot⟩
            · rw [if_neg hji] at hne ⊢
              exact hP j hj hne
        | Err lf =>
          simp only [WP.spec_ok]
          intro e h; cases h
      · rw [if_neg hi3, WP.spec_ok]
        intro e h; cases h; exact hP
    · rw [if_neg hin, WP.spec_ok]
      intro e h; cases h; exact hP
  · exact ⟨by simp, fun j hj hne => absurd (Ipc.exAt_none j hj) hne⟩

/-- **`copy_mrs`' second loop writes only receive-buffer words.** -/
theorem copy_mrs_loop1_wr {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} (hP : EPlaced T E R B) (s : S)
    {sw rw : U64} {rp : Fl4Spec.Word} (hmr : BufMap B rw rp) (n i0 : U64) :
    msg.copy_mrs_loop1 st s sw rw n i0 ⦃ r => P1.WritesIn st s r.2 (EWrite T E R B) ⦄ := by
  unfold msg.copy_mrs_loop1
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val)
    (inv := fun x => P1.WritesIn st s x.1 (EWrite T E R B))
  · rintro ⟨s', i⟩ hW'
    unfold msg.copy_mrs_loop1.body
    simp only at hW' ⊢
    by_cases hc1 : i < n
    · have hlt : i.val < n.val := (P1.gt_iff_val).1 hc1
      have hmax : msg.MSG_MAX_LENGTH.val = 120 := by unfold msg.MSG_MAX_LENGTH; rfl
      by_cases hc2 : i < msg.MSG_MAX_LENGTH
      · have hi120 : i.val < 120 := by rw [← hmax]; exact (P1.gt_iff_val).1 hc2
        simp only [hc1, hc2, ↓reduceIte]
        obtain ⟨i1, h1e, h1v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        rw [h1e, bind_ok]
        have hi1v : i1.val = i.val + 1 := by simpa using h1v
        refine WP.spec_bind (Endp.msg.buf_get.spec s' sw i1) ?_
        rintro v rfl
        refine WP.spec_bind (Endp.msg.buf_set.spec s' rw i1 _) ?_
        rintro s1 rfl
        rw [WP.spec_ok]
        have hwr := hmr i1 (by omega)
        have hal := (hP.balign _ hwr).1
        have hW : P1.WritesIn st s' (L.wr s' (Endp.fl4BufA rw i1) (L.mem s' (Endp.fl4BufA sw i1))) (EWrite T E R B) :=
          (P1.writesIn_wr hal).mono fun b hb => Or.inr (Or.inr (Or.inr ⟨_, hwr, hb⟩))
        exact ⟨(hW'.trans hW).mono fun b h => h.elim id id, by show n.val - i1.val < n.val - i.val; omega⟩
      · simp only [hc1, hc2, ↓reduceIte, WP.spec_ok]
        exact hW'
    · simp only [hc1, ↓reduceIte, WP.spec_ok]
      exact hW'
  · exact P1.WritesIn.refl s _

/-- **`copy_mrs` writes only the receiver's registers and receive-buffer
words** (`EWrite`). -/
theorem copy_mrs_wr {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} (hP : EPlaced T E R B) (s : S)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) (sw rw n : U64)
    (hmr : rw ≠ 0#u64 → ∃ rp, BufMap B rw rp) :
    msg.copy_mrs st s snd sw rcv rw n ⦃ r => P1.WritesIn st s r.2 (EWrite T E R B) ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (Endp.copy_mrs_loop0_spec (L := L) hP s hs hr hne n) ?_
  rintro ⟨s1, i⟩ ⟨-, -, -, hW1⟩
  by_cases h0 : rw = 0#u64
  · simp only [h0, ↓reduceIte]
    show (ok (i, s1)) ⦃ _ ⦄
    rw [WP.spec_ok]; exact hW1
  simp only [h0, ↓reduceIte]
  by_cases h1 : sw = 0#u64
  · simp only [h1, ↓reduceIte]
    show (ok (i, s1)) ⦃ _ ⦄
    rw [WP.spec_ok]; exact hW1
  simp only [h1, ↓reduceIte]
  obtain ⟨rp, hm⟩ := hmr h0
  show (msg.copy_mrs_loop1 st s1 sw rw n i) ⦃ _ ⦄
  refine WP.spec_mono (copy_mrs_loop1_wr hP s1 hm n i) ?_
  intro r h
  exact (hW1.trans h).mono fun b h => h.elim id id

end Live

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`cdt::insert` of a derived cap between two CNode slots at `J`**
(module docstring): the spec's `cap_insert`, `KeepCV`, FL4's slots after
(`insert_trace`), and `JAtZ` after at a new MDB ghost. -/
theorem JAtZ.insDJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ps pd : U64} {rs rd : Nat} (hps : Z.th ps = some (.cnode rs)) (hpd : Z.th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (cc : capability.Cap) (ac : Fl4Spec.Cap) (hca : CapRel cc ac) (hcv : CapValid Z.th cc) (he : EncWf cc)
    (hcnn : cc ≠ .Null) (hsh : shape cc = shape srcC) (hbd : badgeF cc = badgeF srcC ∨ badgeF srcC = 0#u64)
    (hut : isUt srcC = true → ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr (ps.bv, idxs))) (hzb : isZb srcC = false)
    (hkey : okey cc = okey srcC)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC → Vs.VCapOK P L4 L3 L2 L1 cc)
    (htu : Vs.TabUn cc → Vs.TabUn srcC)
    (huc : isUt srcC = true → cc = srcC) (hnat : Vs.NativeCap srcC → Vs.NativeCap cc)
    (hDs : DestCap Z.th (L.mem s) ps) (hDd : DestCap Z.th (L.mem s) pd) :
    cdt.insert st s cc (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' => ∃ σ',
      Fl4Spec.capInsert (Z := Unit) ac (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
      KeepCV σ σ' ∧ Ipc.CnK σ σ' ∧ L.ksb s' = L.ksb s ∧
      (∀ y, IsSlot Z.th y → y ≠ cslotAddr (ps.bv, idxs) → y ≠ cslotAddr (pd.bv, idxd) →
        capV (L.mem s') y = capV (L.mem s) y) ∧
      capV (L.mem s') (cslotAddr (pd.bv, idxd)) = cc ∧
      capV (L.mem s') (cslotAddr (ps.bv, idxs)) = (fullF srcC cc).getD srcC ∧
      ∃ G' : MdbGhost, JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac Lst D s' a σ' ⦄ := by
  have hX := J.xtop
  obtain ⟨hPl, ⟨hSt, hV, hM, hC, hI⟩, hFI, -, hMO, -, -⟩ := hX.rel
  have hAs : AbsSlot Z.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsm : cslotAddr (ps.bv, idxs) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, srcC, hsrcC, hsnn⟩
  have hdnm : cslotAddr (pd.bv, idxd) ∉ Z.G.chains.flatten := fun h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h; rw [hdst] at h0; exact hn (eq_of_ok_eq h0).symm
  have hsd : cslotAddr (ps.bv, idxs) ≠ cslotAddr (pd.bv, idxd) := fun e => by
    rw [e, hdst] at hsrcC; exact hsnn (eq_of_ok_eq hsrcC).symm
  refine WP.spec_mono (WP.spec_and (WP.spec_and (insert_full_finG Z.th s σ Z.G hSt hV hPl hM hC hI hFI hps hpd hls
    hld hsrcC hsnn hdst cc ac hca hcv he hcnn hsh hbd hut hzb hkey hv)
    (Vs.insert_trace hPl s Z.G hM hsm hAd.isSlot hdnm hsrcC cc he))
    (insert_delinv_imp hPl s Z.G hM hsm hAd.isSlot hdnm hsrcC cc he hcnn (by rw [isZb_of_shape hsh]; exact hzb))) ?_
  rintro s' ⟨⟨⟨σ', G', hci, hSt', hV', hM', hC', hI', hFI', hstep, hG'⟩, hF, hoth, hdc, hsc⟩, hdi⟩
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) ac (ps.bv, idxs) (pd.bv, idxd) σ).1 := by rw [hci]; rfl
  have hcn := capInsert_nkn ac _ _ σ _ hmem
  have hkc : KeepC σ σ' := keepC_of hcn (capInsert_nko ac _ _ σ _ hmem) (by
    rintro p (rfl | hp)
    · obtain ⟨cs, h, -⟩ := hSt.cnode ps rs hps; exact ⟨rs, cs, h⟩
    · rw [Set.mem_singleton_iff.1 hp]; obtain ⟨cs, h, -⟩ := hSt.cnode pd rd hpd; exact ⟨rd, cs, h⟩)
  have hMO' : MdbOKV (L.ksb s) (L.mem s') G' := (hstep huc).okv hMO
  have hw : P1.WritesIn st s s' (InSlot Z.th) := by
    refine ⟨hF.1, hF.2.1, fun b hb hn => hF.2.2 b hb fun ⟨y, k, hy, hk', e⟩ => hn ⟨y, hy, ?_⟩⟩
    have hf := hy.fit hPl
    have := hk'.lt
    have hv := wordOf_val (a := y) (k := k) (by omega)
    rw [e, hv]; omega
  have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
    ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
  have hsv : capV (L.mem s) (cslotAddr (ps.bv, idxs)) = srcC := capV_of_capAt hsrcC
  have hdv : capV (L.mem s) (cslotAddr (pd.bv, idxd)) = .Null := capV_of_capAt hdst
  have hsb : ∀ p sb fi d, srcC = .Untyped p sb fi d → sb.val < 64 := fun _ _ _ _ e => by
    have h := hsrcC; rw [capAt_words, e] at h; exact (decode_encWf h).2
  have hTS : ∀ n, n < tcbSlots → ∀ t, Z.th t = some .tcb →
      capAt (L.mem s') (slotOf t n) = capAt (L.mem s) (slotOf t n) := by
    intro n hn t ht
    have hi : IsSlotAt Z.th t n := Or.inr ⟨ht, hn⟩
    rw [capAt_capV, capAt_capV, hoth _ ⟨t, n, hi, rfl⟩ (slotOf_ne_cn hPl hi ht hps hls)
      (slotOf_ne_cn hPl hi ht hpd hld)]
  have hX1 := XTopAt.slotStep hX hw' hcn hkc ⟨hSt', hV', hM', hC', hI'⟩ hFI' hMO' (hTS 1 (by decide))
  have hCU := coverUt_ins hAs.isSlot hsd hsv hdv hdc hsc hoth hsh huc hsb
  have horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl := by
    intro sl h
    by_cases e : sl = (pd.bv, idxd)
    · right; rw [e]; exact hAd
    · left; rw [← capInsert_orig ac _ _ σ ((), σ') hmem sl e]; exact h
  have hUS : UtSrc Z.th (L.mem s) (L.mem s') σ σ' :=
    utSrc_ins hPl hM hC hC' hAs hsv hdv hdc hsc hoth hsh huc hut hsb hG'
      (fun hu => by rw [huc hu]; exact isPF_ut hI hsm hsv hu _)
  have hW : ∀ sl ∈ [(ps.bv, idxs), (pd.bv, idxd)], ∃ p r, sl.1 = p.bv ∧ Z.th p = some (.cnode r) ∧
      sl.2.length = r ∧ DestCap Z.th (L.mem s) p := by
    intro sl hsl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl
    exacts [⟨ps, rs, rfl, hps, hls, hDs⟩, ⟨pd, rd, rfl, hpd, hld, hDd⟩]
  have hWC := hW
  replace hW : ∀ sl ∈ [(ps.bv, idxs), (pd.bv, idxd)], ∃ p r, sl.1 = p.bv ∧ Z.th p = some (.cnode r) ∧
      sl.2.length = r ∧ DestLive Z.th (L.mem s) (L.ksb s) p := fun sl hsl => by
    obtain ⟨p, r, h1, h2, h3, h4⟩ := hWC sl hsl
    exact ⟨p, r, h1, h2, h3, h4.live _⟩
  have hcW : ∀ y, IsSlot Z.th y → (∀ sl ∈ [(ps.bv, idxs), (pd.bv, idxd)], y ≠ cslotAddr sl) →
      capV (L.mem s') y = capV (L.mem s) y :=
    fun y hy hne => hoth y hy (hne _ (by simp)) (hne _ (by simp))
  have hoW : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ [(ps.bv, idxs), (pd.bv, idxd)] := by
    intro sl h
    by_cases e : sl = (pd.bv, idxd)
    · right; rw [e]; simp
    · left; rw [← capInsert_orig ac _ _ σ ((), σ') hmem sl e]; exact h
  have hkcT : KeepCT σ σ' := KeepCT.of_cnK hcn
  have hX1' : XTopAt (L := L) AR (Z.mv G' Z.vs) s' a σ' := hX1
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e
  have hutc := J.cn_utc arI [(ps.bv, idxs), (pd.bv, idxd)] hW hcW hoW hUS hw hgp hM'
  have hjc := J.jcov_cover hw.1 hM' hCU.1 hCU.2
    (fun q hq => J.deadP_slot hX1' hcn hkcT hw (J.jcov.dead q hq))
    (J.idleW_keep hX1'.fin.1.1.1 (CnStep.of_cnK hcn).idle (CnStep.of_cnK hcn).isc)
  have hfh' : ∀ t, Z.th t = some .tcb → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) =
        .Endpoint ep b0 b1 b2 b3 b4 := by
    intro t ht
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have e := hTS 3 (by decide) t ht
    rw [capAt_capV, capAt_capV] at e
    rw [cslot_tcb3, eq_of_ok_eq e, ← cslot_tcb3]; exact hJ.fh t ht
  obtain ⟨hJC, R⟩ := jowes_slotDF J hX1' hcn hkcT hw hFI' hMO' (capInsert_nkz ac _ _ σ _ hmem)
    (typedKept_ins hAs.isSlot hsv hoth hdc hsc hsh) hfh'
    (let ⟨_, _, hJ⟩ := J.jpl; hJ.bfsT fun t ht => Or.inl (hTS 2 (by decide) t ht)) (hdi J.del) hCU.2 hjc horig hutc
  have hvT := vsSlotsT_insert hAs.isSlot hoth hdc (by rw [hsv]; exact hsc) (by rw [hsv]; exact hv)
    (by rw [hsv]; exact htu) (by rw [hsv]; exact hkey) (by rw [hsv]; exact hnat)
  -- `LiveDN` after (LiveFrame's `wstepC`: both written slots in CNodes named by CNode caps)
  have hsA : CapSimL ((fullF srcC cc).getD srcC) srcC := capSimL_fullF srcC cc
  have hZf : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n →
      ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s) y0 = .Zombie p zt n := fun y hy p zt n h => by
    by_cases eD : y = cslotAddr (pd.bv, idxd)
    · subst eD; rw [hdc] at h; subst h
      have := isZb_of_shape hsh; rw [hzb] at this; simp [isZb] at this
    by_cases eS : y = cslotAddr (ps.bv, idxs)
    · subst eS; rw [hsc] at h
      exact ⟨_, hAs.isSlot, by rw [hsv]; exact (hsA.zombie p zt n).1 h⟩
    · exact ⟨y, hy, by rw [← hoth y hy eS eD]; exact h⟩
  have hLv' := LiveDN.wstepC J J.live hX1'
    (fun q hq => J.deadP_slot hX1' hcn hkcT hw (J.jcov.dead q (J.zD q hq))) hcn.idle hw
    [(ps.bv, idxs), (pd.bv, idxd)] hWC hcW hoW
    (fun sl hsl h => by
      exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hsl
      rcases hsl with rfl | rfl
      · rw [hsc] at h; exact hsnn ((hsA.null).1 h)
      · rw [hdc] at h; exact hcnn h)
    hZf
    (fun y0 hy0 hn => by
      by_cases eD : y0 = cslotAddr (pd.bv, idxd)
      · subst eD; exact absurd hdv hn
      by_cases eS : y0 = cslotAddr (ps.bv, idxs)
      · subst eS
        exact ⟨_, hAd.isSlot, by rw [hdc]; exact hcnn, by rw [hdc, hsv]; exact hsh⟩
      · exact ⟨y0, hy0, by rw [hoth y0 hy0 eS eD]; exact hn, by rw [hoth y0 hy0 eS eD]⟩)
  exact ⟨σ', hci, hcn.keepCV hkc, hcn, hw.1, hoth, hdc, hsc, G',
    J.cs_frameV hw.1 hX1' (KBack.of_keepCT hkcT)
      (J.bfK (J.slot2Fr hkcT hX1'.rel.2.1.1 fun q hq => Or.inl (hTS 2 (by decide) q hq)) hvT) hJC R
      (J.vsc.step hvT) (J.ext.step hvT (J.vkeep_slot hw)) hLv' (fun p hp => J.zD p (ZTcb.of_zombies hZf hp))⟩


/-! ## The transfer loop at `J` -/

/-- `JAtZ` at some MDB ghost and VSpace sets, the rest of `Z` and the other
indices fixed. -/
def JM (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (a : A) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ G V, JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ

/-- **The transfer loop's invariant at `J`** (IpcGrant's `TInv` with `JAtZ`
for the composite relation, and the receiver's TCB kept). -/
def TInvJ (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (a : A)
    (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ep : U64) (rb : Fl4Spec.Word) (s0 : S) (σ0 : Fl4Spec.State Unit) (dest0 : U64)
    (slots0 : List Fl4Spec.CslotPtr) (mi0 : Fl4Spec.MessageInfo) (x : S × msginfo.MessageInfo × obj.Slot × U64) :
    Prop :=
  ∃ σ mi slots, x.2.2.2.val ≤ caps.length ∧ MiRel x.2.1 mi ∧ mi.miLength = mi0.miLength ∧
    mi.miLabel = mi0.miLabel ∧
    (∀ r σf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb x.2.2.2.val (caps.drop x.2.2.2.val) slots mi σ =
        ({(r, σf)}, False) →
      Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(r, σf)}, False)) ∧
    JM (L := L) arI AR Z H Cs Ac Lst D a x.1 σ ∧
    (∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rb k) σ) ∧
    (∀ j (hj : j < caps.length), x.2.2.2.val ≤ j →
      ∃ cv, capAt (L.mem x.1) (exAt extra j) = ok cv ∧ UwEq ep cv (caps[j]).1) ∧
    ((x.2.2.1 = 0#u64 ∧ slots = []) ∨
      (x.2.2.1 = dest0 ∧ slots = slots0 ∧ dest0 ≠ 0#u64 ∧ SlotsSame Z.th (L.mem s0) (L.mem x.1))) ∧
    KeepCV σ0 σ ∧ L.ksb x.1 = L.ksb s0 ∧ x.2.1.caps_unwrapped.val < 8

/-- The transfer loop's result at `J`. -/
def TPostJ (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (a : A)
    (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (ep : U64) (rb : Fl4Spec.Word)
    (s0 : S) (σ0 : Fl4Spec.State Unit) (slots0 : List Fl4Spec.CslotPtr) (mi0 : Fl4Spec.MessageInfo)
    (y : S × msginfo.MessageInfo × U64) : Prop :=
  ∃ σ' mf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(mf, σ')}, False) ∧
    MiRel y.2.1 mf ∧ mf.miExtraCaps = BitVec.ofNat 64 y.2.2.val ∧
    y.2.1.caps_unwrapped.val < 8 ∧ y.2.2.val ≤ 3 ∧ mf.miLabel = mi0.miLabel ∧
    KeepCV σ0 σ' ∧ L.ksb y.1 = L.ksb s0 ∧ JM (L := L) arI AR Z H Cs Ac Lst D a y.1 σ'

theorem tpostJ_of {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {ep : U64} {rb : Fl4Spec.Word}
    {σ0 σ : Fl4Spec.State Unit} {slots0 slots : List Fl4Spec.CslotPtr} {mi0 mi : Fl4Spec.MessageInfo} {s s0 : S}
    {out : msginfo.MessageInfo} {i : U64}
    (hmi : MiRel out mi)
    (hch : ∀ r σf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb i.val (caps.drop i.val) slots mi σ =
        ({(r, σf)}, False) →
      Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(r, σf)}, False))
    (hend : Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb i.val (caps.drop i.val) slots mi σ =
      ({(miAt mi i.val, σ)}, False))
    (hcu : out.caps_unwrapped.val < 8) (hi3 : i.val ≤ 3) (hlb : mi.miLabel = mi0.miLabel)
    (hK : KeepCV σ0 σ) (hks : L.ksb s = L.ksb s0) (J : JM (L := L) arI AR Z H Cs Ac Lst D a s σ) :
    TPostJ (L := L) arI AR Z H Cs Ac Lst D a caps ep rb s0 σ0 slots0 mi0 (s, out, i) :=
  ⟨σ, miAt mi i.val, hch _ _ hend, hmi, rfl, hcu, hi3, hlb, hK, hks, J⟩

set_option maxHeartbeats 16000000 in
/-- **One step of the transfer loop at `J`** (IpcGrant's `tc_body`: a badge
into the receive buffer by `JAtZ.userWrJ`, an insert by `JAtZ.insDJ`). -/
theorem tc_bodyJ {rcv : U64} (hrT : Z.th rcv = some .tcb) {x0 : Fl4Spec.Tcb}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rbw : U64} {rb : Fl4Spec.Word} {s0 : S}
    {σ0 : Fl4Spec.State Unit} (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) (hq0 : Endp.ipcBufOf true x0 = some rb)
    (hrw : rbw.bv = rb) {dest0 : U64} {slots0 : List Fl4Spec.CslotPtr} {mi0 : Fl4Spec.MessageInfo}
    (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK Z.th (L.mem s0) (exAt extra j) caps[j])
    (hsrcL : ∀ j (hj : j < caps.length), ∃ ps, (caps[j]).2.1 = ps.bv ∧ DestCap Z.th (L.mem s0) ps)
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (hdest : dest0 ≠ 0#u64 → ∃ d, slots0 = [d] ∧ DestOK Z.th (L.mem s0) dest0 d ∧
      ∃ pd, d.1 = pd.bv ∧ DestCap Z.th (L.mem s0) pd)
    (hm : BufMap Z.B rbw rb) (x : S × msginfo.MessageInfo × obj.Slot × U64)
    (hx : TInvJ (L := L) arI AR Z H Cs Ac Lst D a caps extra ep rb s0 σ0 dest0 slots0 mi0 x) :
    ipc.transfer_caps_loop.body st extra ep rbw x.1 x.2.1 x.2.2.1 x.2.2.2 ⦃ r => match r with
      | .done y => TPostJ (L := L) arI AR Z H Cs Ac Lst D a caps ep rb s0 σ0 slots0 mi0 y
      | .cont x' => TInvJ (L := L) arI AR Z H Cs Ac Lst D a caps extra ep rb s0 σ0 dest0 slots0 mi0 x' ∧
          3 - x'.2.2.2.val < 3 - x.2.2.2.val ⦄ := by
  obtain ⟨s, out, dest, i⟩ := x
  obtain ⟨σ, mi, slots, hi, hmi, hml, hmlb, hch, ⟨G, V, J⟩, hu, hpend, hdst, hK0, hks0, hcu⟩ := hx
  dsimp only at hi hmi hch J hpend hdst hks0 ⊢
  have hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B := J.ip
  have hB : RelTopB (L := L) Z.th G Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := J.xtop.rel
  have hR : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s) σ := J.xtop.ipc
  have hS : SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := ⟨J.xtop.fin.1.1.1, J.xtop.esa⟩
  have hPl : Placed Z.th := hB.1
  have hkr : σ.kheap rcv.bv = some (.tcb x0) := by
    rcases hK0.1 rcv.bv with e | ⟨r, cs, cs', h1, -⟩
    · rw [e, hk0]
    · rw [hk0] at h1; cases h1
  unfold ipc.transfer_caps_loop.body
  by_cases h3 : i < 3#u64
  · have hi3 : i.val < 3 := by scalar_tac
    rw [if_pos h3]
    simp only [lift, bind_ok]
    rw [index_exAt extra _ (by rw [cast_us_val i hi3]; exact hi3), cast_us_val i hi3]
    simp only [bind_ok, obj.Slot.is_null]
    by_cases hlt : i.val < caps.length
    · obtain ⟨ps, rs, idx, cv0, hps, hls, hsl, hxa, hcv0, habs0, hw0, he0, hcvv0⟩ := hsrc i.val hlt
      have hsI : IsSlot Z.th (exAt extra i.val) := by
        rw [hxa]; exact AbsSlot.isSlot (⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩ : AbsSlot Z.th (ps.bv, idx))
      have hne : exAt extra i.val ≠ 0#u64 := hsI.ne_zero hPl
      simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨cv, hcv, huw⟩ := hpend i.val hlt le_rfl
      rw [slot_cap_eq, hcv]
      simp only [bind_ok]
      rw [unwrap_eq]
      simp only [bind_ok]
      have hdrop : caps.drop i.val = caps[i.val] :: caps.drop (i.val + 1) := List.drop_eq_getElem_cons hlt
      by_cases hu' : UnwrapP ep (absCap cv)
      · rw [if_pos hu']
        simp only [buf_caps_eq, bind_ok]
        have hk : (core.num.U64.wrapping_add 122#u64 i).val = 122 + i.val := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        refine WP.spec_bind (buf_set_top hP0 hB hR hS hm (k := core.num.U64.wrapping_add 122#u64 i)
          (by rw [hk]; omega) (epBadgeW cv) (hu _ (by rw [hk]; omega))) ?_
        rintro s2 ⟨rfl, hst, -, -, -⟩
        try simp only [lift, bind_ok]
        have hand : (i &&& 63#u64).val = i.val := by
          rw [UScalar.val_and]
          have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
          rcases this with h | h | h <;> rw [h] <;> rfl
        obtain ⟨i6, h6e, h6v, h6⟩ := spec_exists (U64.ShiftLeft_spec 1#u64 (i &&& 63#u64) (by rw [hand]; omega))
        have hi6 : i6.val < 8 := by
          rw [h6v, hand]
          rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with h | h | h <;> rw [h] <;>
            simp [U64.size, U64.numBits]
        rw [h6e]
        simp only [bind_ok]
        obtain ⟨i8, h8e, h8⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        rw [h8e, bind_ok, WP.spec_ok]
        have hi8 : i8.val = i.val + 1 := by simpa using h8
        set σ1 := setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr rb (core.num.U64.wrapping_add 122#u64 i).val)
          (epBadgeW cv).bv) with hσ1
        have hwp := hm _ (by rw [hk]; omega : (core.num.U64.wrapping_add 122#u64 i).val < 128)
        have hal := (hP0.e.balign _ hwp).1
        have hSS : SlotsSame Z.th (L.mem s) (L.mem (L.wr s (fl4BufA rbw (core.num.U64.wrapping_add 122#u64 i))
            (epBadgeW cv))) :=
          slotsSame_wr hPl s _ hal fun a ha h => hB.2.2.2.2.2.1.slot _
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hwp, le_refl _, by omega⟩)))) a ha h
        -- `JAtZ` after the badge word
        obtain ⟨hOK, -, hBP⟩ := J.xferH
        obtain ⟨hAp, hObj⟩ := J.bufWord hOK hrT hkr hq0 (core.num.U64.wrapping_add 122#u64 i).val
          (by rw [hk]; omega) (b := fl4BufA rbw (core.num.U64.wrapping_add 122#u64 i)) (by rw [fl4BufA_bv, hrw])
        have J2 := J.userWrJ hBP hwp hAp hObj (epBadgeW cv)
        have hks2 : L.ksb (L.wr s (fl4BufA rbw (core.num.U64.wrapping_add 122#u64 i)) (epBadgeW cv)) = L.ksb s :=
          (P1.writesIn_wr (L := L) (s := s) (v := epBadgeW cv) hal).1
        refine ⟨⟨σ1, miUnwrap mi i.val, slots, by rw [hi8]; omega, ⟨hmi.1, ?_, hmi.2.2⟩, hml, hmlb, ?_,
          ⟨G, V, J2⟩, fun k hk => (inUserFrame_setUm _ _ _).2 (hu k hk), fun j hj hij => ?_, ?_,
          ⟨fun p => hK0.1 p, hK0.2⟩, hks2.trans hks0,
          by show (out.caps_unwrapped ||| i6).val < 2 ^ 3; rw [UScalar.val_or]; exact Nat.or_lt_two_pow hcu hi6⟩,
          by rw [hi8]; omega⟩
        · show (out.caps_unwrapped ||| i6).bv = mi.miCapsUnwrapped ||| ((1 : Fl4Spec.Data) <<< i.val)
          rw [UScalar.bv_or, h6, hand]; exact congrArg₂ (· ||| ·) hmi.2.1 rfl
        · intro r σf hr
          refine hch r σf ?_
          rw [hdrop]
          refine tcl_badge (hc := huw.1.mp hu') ?_
            (by rw [hi8] at hr; exact hr)
          unfold Fl4Spec.setExtraBadge
          show Fl4Spec.storeWordOffs rb (Fl4Spec.bufferCptrIndex + i.val) (Fl4Spec.capEpBadge (caps[i.val]).1) σ = _
          rw [← huw.2 (huw.1.mp hu')]
          rw [show Fl4Spec.bufferCptrIndex + i.val = (core.num.U64.wrapping_add 122#u64 i).val by
            rw [hk]; rfl]
          exact hst
        · obtain ⟨cv', h1, h2⟩ := hpend j hj (by rw [hi8] at hij; omega)
          exact ⟨cv', by rw [hSS.capAt (by
            obtain ⟨ps', rs', idx', cv'', hps', hls', -, hxa', -⟩ := hsrc j hj
            rw [hxa']; exact AbsSlot.isSlot (⟨ps', rfl, Or.inl (by simpa [hls'] using hps')⟩ :
              AbsSlot Z.th (ps'.bv, idx')))]; exact h1, h2⟩
        · rcases hdst with h | ⟨h1, h2, h3', h4⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, h2, h3', SlotsSame.trans' h4 hSS⟩
      · rw [if_neg hu']
        simp only []
        rcases hdst with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hd0, hSS⟩
        · simp only [decide_true, ↓reduceIte, WP.spec_ok]
          refine tpostJ_of hmi hch ?_ hcu (by omega) hmlb hK0 hks0 ⟨G, V, J⟩
          rw [hdrop]
          exact tcl_noslot (fun h => hu' (huw.1.mpr h))
        · obtain ⟨d, hsl0, ⟨pd, rd, idxd, hpd, hld, rfl, hdA, hdN⟩, pd', hpd1, hDd0⟩ := hdest hd0
          have epd : pd' = pd := P1.eq_of_bv hpd1.symm
          rw [epd] at hDd0
          subst hsl0
          simp only [hd0, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hcvs : capAt (L.mem s) (exAt extra i.val) = ok cv0 := by rw [hSS.capAt hsI, hcv0]
          rw [hcv] at hcvs
          have hcvs' : cv = cv0 := by simpa using hcvs
          subst hcvs'
          have hsl' : (caps[i.val]).2 = (ps.bv, idx) := hsl
          obtain ⟨ps', hps1, hDs0⟩ := hsrcL i.val hlt
          rw [hsl'] at hps1
          have eps : ps' = ps := P1.eq_of_bv hps1.symm
          rw [eps] at hDs0
          have hnot : ¬ UnwrapP ep (caps[i.val]).1 := fun h => hu' (huw.1.mpr h)
          have hAs : AbsSlot Z.th (ps.bv, idx) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
          have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
          have hdI : IsSlot Z.th dest := by rw [hdA]; exact hAd.isSlot
          have hncs : cv ≠ .Null → NoChildrenRel (st := st) s σ (exAt extra i.val) (caps[i.val]).2 := by
            intro hut
            obtain ⟨-, ⟨-, -, hM, hC, hI⟩, -⟩ := hB
            rw [hsl', hxa]
            refine noChildren_of_adj Z.th hPl s σ G hM hC (hI.parentAdj (th := Z.th)) _ hAs
              ((hM.members _).2 ⟨hAs.isSlot, cv, by rw [← hxa]; exact hcv, ?_⟩)
            exact hut
          obtain ⟨r, hr, r', hr', hdr⟩ := derive_rel (Z := Unit) s σ (exAt extra i.val) (caps[i.val]).2 cv hw0 he0
            (fun h => hncs (by rintro rfl; exact h))
          rw [← habs0] at hr'
          rw [hr]
          simp only [bind_ok]
          cases r with
          | Err e =>
            cases r' with
            | ok _ => exact hdr.elim
            | error e' =>
              simp only [WP.spec_ok]
              refine tpostJ_of hmi hch ?_ hcu (by omega) hmlb hK0 hks0 ⟨G, V, J⟩
              rw [hdrop]
              exact tcl_derr hnot hr'
          | Ok c' =>
            cases r' with
            | error _ => exact hdr.elim
            | ok a' =>
              obtain ⟨hw', ha', he', hv', hk'⟩ := hdr
              simp only []
              by_cases hn : c' = .Null
              · subst hn
                rw [cap_is_null_null]
                simp only [bind_ok, ↓reduceIte, WP.spec_ok]
                refine tpostJ_of hmi hch ?_ hcu (by omega) hmlb hK0 hks0 ⟨G, V, J⟩
                rw [hdrop]
                rw [← ha'] at hr'
                exact tcl_dnull hnot hr'
              · rw [cap_is_null_ne hn]
                simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
                have hcvn : cv ≠ .Null := by
                  rintro rfl; unfold objects.derive_cap at hr; simp at hr; exact hn hr.symm
                obtain ⟨hsh, hbd, hzb, hnu⟩ := derive_shape hr hn (hncs hcvn)
                have hsnn : cv ≠ .Null := fun h => hn ((Vs.shape_kind hsh).2.2.2.2.2 h)
                have hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idx)) = ok cv := by rw [← hxa]; exact hcv
                have hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null := by
                  rw [← hdA, hSS.capAt hdI]; exact hdN
                have hut : isUt cv = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idx)) := by
                  intro hu0 y hy
                  obtain ⟨z, hz⟩ := desc_tail_child hy
                  exact hnu hu0 (by rw [hsl']; exact (hB.2.1.2.2.2.1.has_child_iff hPl hAs).2 ⟨z, hz⟩)
                have hsI' : IsSlot Z.th (cslotAddr (ps.bv, idx)) := hAs.isSlot
                have hnx : nextOf (L.mem s) (cslotAddr (ps.bv, idx)) = 0#u64 ∨
                    IsSlot Z.th (nextOf (L.mem s) (cslotAddr (ps.bv, idx))) := by
                  have hm' := (hB.2.1.2.2.1.members _).2 ⟨hsI', cv, hsrcC, hsnn⟩
                  rcases hB.2.1.2.2.1.next_mem hm' with h | ⟨h, -⟩
                  · exact Or.inl h
                  · exact Or.inr ((hB.2.1.2.2.1.members _).1 h).1
                have hDs : DestCap Z.th (L.mem s) ps := hDs0.same hSS
                have hDd : DestCap Z.th (L.mem s) pd := hDd0.same hSS
                have hins := WP.spec_and (J.insDJ hps hpd hls hld hsrcC hsnn hdst c' a' ⟨hw', ha'⟩
                  (hv' Z.th hcvv0) he' hn hsh (Or.inl hbd) hut hzb (derive_okey hr hn)
                  (fun P L4 L3 L2 L1 => derive_vcap hr P L4 L3 L2 L1) (fun h => (derive_tabun hr h).elim)
                  (derive_ut hr) (derive_nat hr) hDs hDd)
                  (insert_capfr2 hPl s c' _ _ hsI' hAd.isSlot cv hsrcC he0 he' hnx)
                rw [← hxa, ← hdA] at hins
                refine WP.spec_bind hins ?_
                rintro s2 ⟨⟨σ2, hci, hK2, hcn2, hks2, -, -, -, G2, J2⟩, hfr⟩
                obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
                rw [h3e, bind_ok, WP.spec_ok]
                have hi3v : i3.val = i.val + 1 := by simpa using h3v
                refine ⟨⟨σ2, mi, [], by rw [hi3v]; omega, hmi, hml, hmlb, fun r σf hr0 => ?_, ⟨G2, V, J2⟩,
                  fun k hk => hcn2.inUserFrame (hu k hk), fun j hj hij => ?_, Or.inl ⟨rfl, rfl⟩, hK0.trans hK2,
                  hks2.trans hks0, hcu⟩, by rw [hi3v]; omega⟩
                · refine hch r σf ?_
                  rw [hdrop]
                  refine tcl_insert hnot hr' (fun h => hn ((CapRel.null_iff ⟨hw', ha'⟩).1 h)) ?_
                    (by rw [hi3v] at hr0; exact hr0)
                  show Fl4Spec.capInsert a' (caps[i.val]).2 (pd.bv, idxd) σ = _
                  rw [hsl']; exact hci
                · obtain ⟨cv', h1, h2⟩ := hpend j hj (by rw [hi3v] at hij; omega)
                  obtain ⟨ps2, rs2, idx2, cv'', hps2, hls2, -, hxa2, -⟩ := hsrc j hj
                  have hjI : IsSlot Z.th (exAt extra j) := by
                    rw [hxa2]; exact AbsSlot.isSlot (⟨ps2, rfl, Or.inl (by simpa [hls2] using hps2)⟩ :
                      AbsSlot Z.th (ps2.bv, idx2))
                  obtain ⟨-, -, -, cvj, -, -, -, -, hcvj, habsj, -⟩ := hsrc j hj
                  have hsrcfull : ∀ c'', fullF cv c' = some c'' → ¬ UnwrapP ep (absCap cv) := fun c'' hf =>
                    not_unwrap_of_ut (by
                      cases cv <;> simp [fullF] at hf
                      exact ⟨_, _, _, _, rfl⟩)
                  by_cases ejd : exAt extra j = dest
                  · refine ⟨c', by rw [ejd]; exact hfr.2.1, ?_, fun h => ?_⟩
                    · rw [ejd, hdN] at hcvj
                      have : cvj = .Null := by simpa using hcvj.symm
                      rw [habsj, this]
                      refine ⟨fun h => absurd ((unwrap_shape ep cv).2 (hsh ▸ (unwrap_shape ep c').1 h)) hu',
                        fun h => absurd h not_unwrap_of_null⟩
                    · rw [ejd, hdN] at hcvj
                      have : cvj = .Null := by simpa using hcvj.symm
                      rw [habsj, this] at h; exact absurd h not_unwrap_of_null
                  · rcases hfr.2.2 _ hjI ejd with heq | ⟨ejs, c'', hfc, hc''⟩
                    · exact ⟨cv', by rw [heq]; exact h1, h2⟩
                    · rw [ejs, hcv0] at hcvj
                      have : cvj = cv := by simpa using hcvj.symm
                      have hnu := hsrcfull c'' hfc
                      have hnu'' := not_unwrap_of_ut (ep := ep) (fullF_ut hfc)
                      refine ⟨c'', hc'', ⟨fun h => absurd h hnu'', fun h => ?_⟩, fun h => ?_⟩
                      · rw [habsj, this] at h; exact absurd h hnu
                      · rw [habsj, this] at h; exact absurd h hnu
    · have hieq : i.val = caps.length := by omega
      rw [hnull i.val (by omega) hi3]
      simp only [decide_true, ↓reduceIte, WP.spec_ok]
      refine tpostJ_of hmi hch ?_ hcu (by omega) hmlb hK0 hks0 ⟨G, V, J⟩
      rw [hieq, List.drop_length, ← hieq]
      exact tcl_nil _ _ _
  · rw [if_neg h3]
    simp only [WP.spec_ok]
    have hieq : i.val = caps.length := by
      have : 3 ≤ i.val := by scalar_tac
      omega
    refine tpostJ_of hmi hch ?_ hcu (by omega) hmlb hK0 hks0 ⟨G, V, J⟩
    rw [hieq, List.drop_length, ← hieq]
    exact tcl_nil _ _ _


/-- FL4's receive slot in a live CNode (`get_receive_slot_live`) and as
`DestConf`, so the destination's CNode is live. -/
theorem destLive_of {th : TypedHeap} (hP : Placed th) {m : U64 → U64}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {extra : Aeneas.Std.Array obj.Slot 3#usize} {dest : U64}
    {slots : List Fl4Spec.CslotPtr} (hD : DestConf th m caps extra dest slots)
    (hL : dest ≠ 0#u64 → ∃ pd idx, dest = cslotAddr (pd.bv, idx) ∧ th pd = some (.cnode idx.length) ∧
      DestCap th m pd) :
    dest ≠ 0#u64 → ∃ d, slots = [d] ∧ DestOK th m dest d ∧ ∃ pd, d.1 = pd.bv ∧ DestCap th m pd := by
  intro h0
  rcases hD with ⟨h, -⟩ | ⟨-, d, hsl, hok⟩
  · exact absurd h h0
  obtain ⟨pd, idx, he, hpd, hDL⟩ := hL h0
  have hok' := hok
  obtain ⟨pd0, rd0, idx0, hpd0, hl0, rfl, he0, -⟩ := hok'
  have e := cslotAddr_inj hP (⟨pd0, rfl, Or.inl (by rw [hl0]; exact hpd0)⟩ : AbsSlot th (pd0.bv, idx0))
    (⟨pd, rfl, Or.inl hpd⟩ : AbsSlot th (pd.bv, idx)) (he0.symm.trans he)
  exact ⟨_, hsl, hok, pd, congrArg Prod.fst e, hDL⟩

set_option maxHeartbeats 8000000 in
/-- **The transfer loop at `J`** (IpcGrant's `transfer_loop_top`). -/
theorem transfer_loopJ {rcv : U64} (hrT : Z.th rcv = some .tcb) {x0 : Fl4Spec.Tcb}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rbw : U64}
    {rb : Fl4Spec.Word} {s0 : S} {σ0 : Fl4Spec.State Unit} (hk0 : σ0.kheap rcv.bv = some (.tcb x0))
    (hq0 : Endp.ipcBufOf true x0 = some rb) (hrw : rbw.bv = rb) {dest0 : U64} {slots0 : List Fl4Spec.CslotPtr}
    {mi0 : Fl4Spec.MessageInfo} (out0 : msginfo.MessageInfo) (hmi0 : MiRel out0 mi0)
    (hcu0 : out0.caps_unwrapped.val < 8) (J0 : JM (L := L) arI AR Z H Cs Ac Lst D a s0 σ0) (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK Z.th (L.mem s0) (exAt extra j) caps[j])
    (hsrcL : ∀ j (hj : j < caps.length), ∃ ps, (caps[j]).2.1 = ps.bv ∧ DestCap Z.th (L.mem s0) ps)
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (hD : DestConf Z.th (L.mem s0) caps extra dest0 slots0)
    (hDL : dest0 ≠ 0#u64 → ∃ pd idx, dest0 = cslotAddr (pd.bv, idx) ∧ Z.th pd = some (.cnode idx.length) ∧
      DestCap Z.th (L.mem s0) pd)
    (hm : BufMap Z.B rbw rb) (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rb k) σ0) :
    ipc.transfer_caps_loop st s0 extra ep rbw out0 dest0 0#u64 ⦃ y =>
      TPostJ (L := L) arI AR Z H Cs Ac Lst D a caps ep rb s0 σ0 slots0 mi0 y ⦄ := by
  obtain ⟨G0, V0, J00⟩ := J0
  have hdest := destLive_of J00.xtop.rel.1 hD hDL
  unfold ipc.transfer_caps_loop
  refine loop.spec_decr_nat (fun x => 3 - x.2.2.2.val)
    (TInvJ (L := L) arI AR Z H Cs Ac Lst D a caps extra ep rb s0 σ0 dest0 slots0 mi0) _ _ _ (fun x hx => ?_) ?_
  · obtain ⟨s, o, d, i⟩ := x
    have h := tc_bodyJ hrT hk0 hq0 hrw hlen hsrc hsrcL hnull hdest hm (s, o, d, i) hx
    refine WP.spec_mono h ?_
    intro r hr
    cases r with
    | done y => exact hr
    | cont x' => exact hr
  · refine ⟨σ0, mi0, slots0, by simp, hmi0, rfl, rfl, fun r σf h => by simpa using h, ⟨G0, V0, J00⟩, hu,
      fun j hj _ => ?_, ?_, KeepCV.refl σ0, rfl, hcu0⟩
    · obtain ⟨ps, rs, idx, cv, -, -, -, -, hcv, habs, -⟩ := hsrc j hj
      exact ⟨cv, hcv, UwEq.of_abs habs.symm⟩
    · rcases hD with ⟨h0, h1⟩ | ⟨h0, -⟩
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨rfl, rfl, h0, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

set_option maxHeartbeats 8000000 in
/-- **`transfer_caps` at `J`** (IpcGrant's `transfer_caps_top` with the
receive slot's CNode live, `get_receive_slot_live`). -/
theorem transfer_capsJ {rcv : U64} (hrT : Z.th rcv = some .tcb) {x0 : Fl4Spec.Tcb}
    {s : S} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hk0 : σ.kheap rcv.bv = some (.tcb x0)) {rp : Fl4Spec.Word} (hq0 : Endp.ipcBufOf true x0 = some rp)
    (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo)
    (hil : info.length.bv = mi.miLength) (hlb : info.label.bv = mi.miLabel)
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK Z.th (L.mem s) (exAt extra j) caps[j])
    (hsrcL : ∀ j (hj : j < caps.length), ∃ ps, (caps[j]).2.1 = ps.bv ∧ DestCap Z.th (L.mem s) ps)
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (ep : U64) (rbw : U64) (hrw : rbw.bv = rp) (hr0 : rbw ≠ 0#u64) (hm : BufMap Z.B rbw rp)
    (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rp k) σ) :
    ipc.transfer_caps st s info extra ep rcv rbw ⦃ r => ∃ σ' mf,
      Fl4Spec.transferCaps (Z := Unit) mi caps (some ep.bv) rcv.bv (some rp) σ = ({(mf, σ')}, False) ∧
      MiRel r.1 mf ∧ r.1.extra_caps.bv = mf.miExtraCaps ∧
      r.1.caps_unwrapped.val < 8 ∧ r.1.extra_caps.val ≤ 3 ∧ mf.miLabel = mi.miLabel ∧
      KeepCV σ σ' ∧ L.ksb r.2 = L.ksb s ∧ JM (L := L) arI AR Z H Cs Ac Lst D a r.2 σ' ⦄ := by
  have hmi0 : MiRel { label := info.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := info.length }
      ⟨mi.miLength, 0, 0, mi.miLabel⟩ := ⟨hil, rfl, hlb⟩
  have hJ0 : JM (L := L) arI AR Z H Cs Ac Lst D a s σ := ⟨Z.G, Z.vs, J⟩
  have hB := J.xtop.rel
  have hI := J.xtop.irelK J.ks J.buf
  have hGRs : ∃ sl, Fl4Spec.getReceiveSlots (Z := Unit) rcv.bv (some rp) σ = ({(sl, σ)}, False) := by
    obtain ⟨dest, sl, hsl, -⟩ := WP.spec_exists (Ipc.get_receive_slot_top J.ip hB hI.1.toE hrT hm hr0 caps extra)
    exact ⟨sl, hsl⟩
  have hnil : caps = [] → Fl4Spec.transferCaps (Z := Unit) mi caps (some ep.bv) rcv.bv (some rp) σ =
      ({(⟨mi.miLength, 0, 0, mi.miLabel⟩, σ)}, False) := by
    rintro rfl
    obtain ⟨sl, hsl⟩ := hGRs
    unfold Fl4Spec.transferCaps
    rw [nd_bind_one hsl, nd_pure_bind']
    exact tcl_nil _ _ _
  unfold ipc.transfer_caps msginfo.MessageInfo.new
  simp only [bind_ok]
  rw [index_exAt extra 0#usize (by decide), show ((0#usize : Usize).val) = 0 from rfl]
  simp only [bind_ok, obj.Slot.is_null]
  by_cases h0 : exAt extra 0 = 0#u64
  · have hcn : caps = [] := by
      cases caps with
      | nil => rfl
      | cons y ys =>
        exfalso
        obtain ⟨ps, rs, idx, cv, hps, hls, -, hxa, -⟩ := hsrc 0 (by simp)
        have := (AbsSlot.isSlot (⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩ : AbsSlot Z.th (ps.bv, idx))).ne_zero hB.1
        rw [← hxa] at this; exact this h0
    rw [decide_eq_true h0, if_pos rfl, WP.spec_ok]
    exact ⟨σ, ⟨mi.miLength, 0, 0, mi.miLabel⟩, hnil hcn, hmi0, rfl, by simp, by simp, rfl, KeepCV.refl σ, rfl, hJ0⟩
  · rw [decide_eq_false h0, if_neg Bool.false_ne_true, if_neg hr0]
    refine WP.spec_bind (WP.spec_and (Ipc.get_receive_slot_top J.ip hB hI.1.toE hrT hm hr0 caps extra)
      (get_receive_slot_live Z.th s σ hB.2.1.1 hB.2.1.2.1 hrT rbw)) ?_
    rintro dest ⟨⟨slots, hsl, hD⟩, hDL⟩
    refine WP.spec_bind (transfer_loopJ hrT hk0 hq0 hrw _ hmi0 (by simp) hJ0 hlen hsrc hsrcL hnull hD hDL hm hu) ?_
    rintro ⟨s2, out1, i⟩ ⟨σ', mf, hloop, hmi1, hex, hcu1, hi31, hlb1, hK, hks, J'⟩
    refine (WP.spec_ok _).2 ⟨σ', mf, ?_, hmi1, ?_, hcu1, hi31, hlb1, hK, hks, J'⟩
    swap
    · show i.bv = mf.miExtraCaps
      rw [hex]; apply BitVec.eq_of_toNat_eq
      show i.val = (BitVec.ofNat 64 i.val).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by scalar_tac)]
    unfold Fl4Spec.transferCaps
    rw [nd_bind_one hsl, nd_pure_bind']
    exact hloop

set_option maxHeartbeats 16000000 in
/-- **The register-only `do_ipc_transfer` at `J`, caps looked up**
(XTopJointXfer's `JAtZ.xferRegsJ` with any grant: the extra caps' lookup
by `lookup_extra_top`, read only, its caps dropped with no receive buffer;
the spec's outcome IpcGrantX's `doIpcTransfer_regsG`). -/
theorem JAtZ.xferRegsGJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hOK : Endp.IpcBufCapOK σ)
    (hBC : Endp.BufCover Z.T Z.B σ)
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : Endp.ipcBufOf true xr = none) (epo : Option Fl4Spec.ObjRef) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ =
        ({((), Notif.updK σ rcv.bv (.tcb (Endp.xferTcb xr xs badge.bv)))}, False) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a
        (Notif.updK σ rcv.bv (.tcb (Endp.xferTcb xr xs badge.bv))) ⦄ := by
  have hne' : snd.bv ≠ rcv.bv := fun e => hne (P1.eq_of_bv e)
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hs hks
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have thT : ∀ t ∈ Z.T, Z.th t = some .tcb := fun t ht => (hJ.tcb t).2 (J.zH.1 t ht)
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv =
      xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT rcv hr) hkr hOK true) ?_
  rintro rb ⟨hrb0, -⟩
  have hrb' : rb = 0#u64 := hrb0.2 hrb
  subst hrb'
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  have hft0 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.NullFault := by
    rw [hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT snd hs) hks hOK false) ?_
  rintro sb ⟨hsb, hsbp⟩
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (Endp.msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  obtain ⟨xs', hks', hws⟩ := J.buf snd hs
  rw [hks] at hks'; cases hks'
  have hsm : ∀ sp, Endp.ipcBufOf false xs = some sp → Endp.BufMap Z.B sb sp :=
    fun sp h => hBC snd hs xs false sp hks h sb (hsbp hws sp h)
  have hlkF := Ipc.lookup_extra_top J.ip J.xtop.rel hI.1 (thT snd hs) sb (Endp.ipcBufOf false xs)
    ⟨hsb.1, hsb.2⟩ hsm tag (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register))
    (by show tag.extra_caps.bv.toNat = _; rw [hext, hwmi])
    (by show tag.extra_caps.bv.toNat ≤ 3; rw [hext, hwmi]; exact Endp.extra_le3 _)
  have hspec := Endp.doIpcTransfer_regsG hne' hks hkr hf hrb epo badge.bv grant (fun _ => by
    obtain ⟨r, caps, hc, -⟩ := WP.spec_exists hlkF; exact ⟨caps, hc⟩)
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sb tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ _ => True ⦄ := by
    cases grant with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      refine WP.spec_bind hlkF ?_
      rintro r -
      split <;> simp
  refine WP.spec_bind hex ?_
  rintro extra -
  refine WP.spec_bind (copyMrsJ_norecv J hs hr hne' hks hkr sb tag.length) ?_
  rintro ⟨i, s1⟩ ⟨hi, V1, J1⟩
  refine WP.spec_bind (Endp.transfer_caps_norecv (L := L) s1 tag extra ep rcv) ?_
  rintro ⟨out, s2⟩ hout
  simp only [Prod.mk.injEq] at hout
  obtain ⟨rfl, h2⟩ := hout
  subst s2
  show (do
    let s3 ← msg.set_msg_info st s1 rcv
      { label := tag.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := i }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  have hi4 : i.val ≤ 4 := by rw [hi]; omega
  refine WP.spec_bind (Endp.set_msg_info_spec (L := L) s1 rcv tag.label i (by omega)) ?_
  rintro s3 ⟨v, rfl, hv⟩
  refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ rcv _ badge) ?_
  rintro s4 rfl
  -- the spec's message info
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  have hLv : Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength = tag.length.val := by
    show _ = tag.length.bv.toNat
    rw [hlen, hwmi]
  have hvx : v.bv = Fl4Spec.messageInfoToData (Endp.xferInfo w) := by
    rw [hv]
    unfold Endp.xferInfo
    congr 1
    congr 1
    · exact Endp.xfer_len (by rw [hi]; show _ = min (Fl4Spec.unat _) 4; rw [hLv])
    · rw [hlab, hwmi]; rfl
  set x1 := Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take
    (Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength)) with hx1
  rw [← hLv] at J1
  change JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac Lst D s1 a (Notif.updK σ rcv.bv (.tcb x1)) at J1
  have hkr1 : (Notif.updK σ rcv.bv (.tcb x1)).kheap rcv.bv = some (.tcb x1) := by simp [Notif.updK]
  -- the message info
  have hX2 := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hr hkr1 Fl4Spec.msg_info_register (by decide) v
  obtain ⟨V2, J2⟩ := J1.regWrJ hr hkr1 Fl4Spec.msg_info_register v hX2
  rw [regIdx_msgInfo] at J2
  have hkr2 : (Notif.updK (Notif.updK σ rcv.bv (.tcb x1)) rcv.bv
      (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp [Notif.updK]
  -- the badge
  have hX3 := badge_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hr hkr2 badge
  rw [badgeRegA_eq_regA] at hX3
  obtain ⟨V3, J3⟩ := J2.regWrJ hr hkr2 Fl4Spec.badge_register badge hX3
  rw [regIdx_badge] at J3
  have hfin : Notif.updK (Notif.updK (Notif.updK σ rcv.bv (.tcb x1)) rcv.bv
      (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      Notif.updK σ rcv.bv (.tcb (Endp.xferTcb xr xs badge.bv)) := by
    simp only [Notif.updK, Function.update_idem]
    rw [hvx]; rfl
  refine ⟨hspec, V3, ?_⟩
  rw [← hfin]; exact J3



set_option maxHeartbeats 16000000 in
/-- **`do_ipc_transfer` into a receive buffer at `J`, caps granted** (XTopJointXfer's
`JAtZ.xferBufJ` with the extra caps looked up, `lookup_extra_top` and
`lookup_extra_live`, `copy_mrs` writing no slot, `copy_mrs_wr`, and
`transfer_capsJ`; the spec's outcome IpcGrantX's `doIpcTransfer_grant`). -/
theorem JAtZ.xferGrantJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : Endp.ipcBufOf true xr = some rp) (epo : Option Fl4Spec.ObjRef) (ep badge : U64)
    (grant : Bool) (hepo : epo = some ep.bv ∨ (epo = none ∧ ep = 0#u64)) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      (∀ p, p ≠ rcv.bv → σ'.kheap p = σ.kheap p ∨
        ∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) ∧
      (∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch }) ∧
      JM (L := L) arI AR Z H Cs Ac Lst D a s' σ' ⦄ := by
  have hne' : snd.bv ≠ rcv.bv := fun e => hne (P1.eq_of_bv e)
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hs hks
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have thT : ∀ t ∈ Z.T, Z.th t = some .tcb := fun t ht => (hJ.tcb t).2 (J.zH.1 t ht)
  obtain ⟨hOK, hBC, -⟩ := J.xferH
  have hEP := J.xtop.fin.1.2.ep
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv =
      xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  obtain ⟨xr', hkr', hwr⟩ := J.buf rcv hr
  rw [hkr] at hkr'; cases hkr'
  obtain ⟨xs', hks', hws⟩ := J.buf snd hs
  rw [hks] at hks'; cases hks'
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT rcv hr) hkr hOK true) ?_
  rintro rw ⟨hrw0, hrwp⟩
  have hrwv : rw.bv = rp := hrwp hwr rp hrb
  have hmr : Endp.BufMap Z.B rw rp := hBC rcv hr xr true rp hkr hrb rw hrwv
  have hrwn : rw ≠ 0#u64 := fun e => by have := hrw0.1 e; rw [hrb] at this; cases this
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  have hft0 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.NullFault := by
    rw [hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT snd hs) hks hOK false) ?_
  rintro sw ⟨hsw0, hswp⟩
  have hsw : (Endp.ipcBufOf false xs = none ∧ sw = 0#u64) ∨
      (∃ sp, Endp.ipcBufOf false xs = some sp ∧ sw ≠ 0#u64 ∧ Endp.BufMap Z.B sw sp) := by
    cases h : Endp.ipcBufOf false xs with
    | none => exact Or.inl ⟨rfl, hsw0.2 h⟩
    | some sp =>
      exact Or.inr ⟨sp, rfl, (fun e => by have := hsw0.1 e; rw [h] at this; cases this),
        hBC snd hs xs false sp hks h sw (hswp hws sp h)⟩
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (Endp.msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  have hsb' : sw = 0#u64 ↔ Endp.ipcBufOf false xs = none := ⟨hsw0.1, hsw0.2⟩
  have hsm : ∀ sp, Endp.ipcBufOf false xs = some sp → Endp.BufMap Z.B sw sp :=
    fun sp h => hBC snd hs xs false sp hks h sw (hswp hws sp h)
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sw tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ extra => ∃ caps,
        (if grant = true then Fl4Spec.NonDetE.catch (Fl4Spec.lookupExtraCaps (Z := Unit) snd.bv
          (Endp.ipcBufOf false xs) (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs
            Fl4Spec.msg_info_register))) (fun _ => pure []) else pure []) σ = ({(caps, σ)}, False) ∧
        Ipc.ExtraOK Z.th (L.mem s) extra caps ∧ ExtraLive Z.th (L.mem s) (L.ksb s) extra ⦄ := by
    have hnl : ExtraLive Z.th (L.mem s) (L.ksb s) ipc.NO_EXTRA_CAPS :=
      fun j hj hne => absurd (Ipc.exAt_none j hj) hne
    cases grant with
    | false =>
      rw [if_neg (by decide), WP.spec_ok]
      exact ⟨[], rfl, Ipc.extraOK_none Z.th _, hnl⟩
    | true =>
      rw [if_pos rfl]
      refine WP.spec_bind (WP.spec_and (Ipc.lookup_extra_top J.ip J.xtop.rel hI.1 (thT snd hs) sw
        (Endp.ipcBufOf false xs) hsb' hsm tag _ (by show tag.extra_caps.bv.toNat = _; rw [hext, hwmi])
        (by show tag.extra_caps.bv.toNat ≤ 3; rw [hext, hwmi]; exact Endp.extra_le3 _))
        (lookup_extra_live Z.th s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT snd hs) sw tag)) ?_
      rintro r ⟨⟨caps, hc, hok⟩, hl⟩
      cases r with
      | Ok e => simp only [WP.spec_ok]; exact ⟨caps, by simp only [↓reduceIte]; exact hc, hok, hl _ rfl⟩
      | Err _ => simp only [WP.spec_ok]; exact ⟨caps, by simp only [↓reduceIte]; exact hc, hok, hnl⟩
  refine WP.spec_bind hex ?_
  rintro extra ⟨caps, hlk, hok, hlive⟩
  -- `copy_mrs`
  have hun : Fl4Spec.unat tag.length.bv = tag.length.val := rfl
  set x1 := Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take tag.length.val)
    with hx1
  have hcm : msg.copy_mrs st s snd sw rcv rw tag.length ⦃ r => ∃ σc,
      Fl4Spec.copyMrs (Z := Unit) snd.bv (Endp.ipcBufOf false xs) rcv.bv (some rp) tag.length.bv σ =
        ({(r.1.bv, σc)}, False) ∧
      σc.kheap = Function.update σ.kheap rcv.bv (some (.tcb x1)) ∧ r.1.val ≤ 120 ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.2 a σc ⦄ := by
    unfold msg.copy_mrs
    refine WP.spec_bind (copyMrsJ_loop0 J hs hr hne' hks hkr tag.length) ?_
    rintro ⟨s1, i⟩ ⟨hi, V1, J1⟩
    simp only [hrwn, ↓reduceIte]
    rcases hsw with ⟨hsn, rfl⟩ | ⟨sp, hsp, hsw0', hms⟩
    · simp only [↓reduceIte]
      show (ok (i, s1)) ⦃ _ ⦄
      simp only [WP.spec_ok]
      refine ⟨Notif.updK σ rcv.bv (.tcb x1), ?_, rfl, by rw [hi]; omega, V1, J1⟩
      rw [hsn, Endp.copyMrs_noSendBuf hne' hks hkr _ _, hun]
      congr
      exact (Endp.xfer_len (by rw [hi]; rfl)).symm
    · simp only [hsw0', ↓reduceIte]
      have hk1 : (Notif.updK σ rcv.bv (.tcb x1)).kheap rcv.bv = some (.tcb x1) := by simp [Notif.updK]
      have hq1 : Endp.ipcBufOf true x1 = some rp := by rw [hx1, Endp.ipcBufOf_copyRegs]; exact hrb
      refine WP.spec_mono (copyMrsJ_loop1 (Z := Z.mv Z.G V1) (thT rcv hr)
        hk1 hq1 hmr hrwv hms tag.length i hle hi J1) ?_
      rintro ⟨n2, s2⟩ ⟨hn2, V2, J2⟩
      refine ⟨Endp.setUm (Notif.updK σ rcv.bv (.tcb x1)) (Endp.copyBufMem σ.machineState.underlyingMemory sp rp
        (List.range' 5 (tag.length.val - 4))), ?_, rfl, by show n2.val ≤ 120; rw [hn2]; exact hle, V2, J2⟩
      rw [hsp, Endp.copyMrs_bufs hne' hks hkr sp rp tag.length.bv ?_]
      · have e : n2 = tag.length := UScalar.eq_of_val_eq hn2
        subst e
        rw [← Endp.xfer_len_buf hle, Endp.bufIdx_eq, hun]
      · intro x hx
        rw [Endp.bufIdx_eq] at hx
        have hx' : x < 128 := by simp at hx; omega
        exact ⟨Endp.bufAddr_aligned hEP hms x, Endp.bufAddr_aligned hEP hmr x, buf_frame_of_ok hOK hkr hrb x hx'⟩
  refine WP.spec_bind (WP.spec_and hcm (copy_mrs_wr hEP s hs hr hne sw rw tag.length (fun _ => ⟨rp, hmr⟩))) ?_
  rintro ⟨n, s1⟩ ⟨⟨σc, hcopy, hkcf, hn, V1, J1⟩, hWc⟩
  simp only at hcopy hkcf hn J1 hWc
  have hkc : σc.kheap rcv.bv = some (.tcb x1) := by rw [hkcf]; simp
  have hS1 : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    Ipc.slotsSame_of_iwords J.xtop.rel.1 J.xtop.rel.2.2.2.2.2.1 hWc (fun _ ha => EWrite.iwords ha)
  have hks1 : L.ksb s1 = L.ksb s := hWc.1
  have hok1 := hok.of_same hS1
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  have hlenw : tag.length.bv = (Fl4Spec.dataToMessageInfo w).miLength := by rw [hlen, hwmi]
  have hlabw : tag.label.bv = (Fl4Spec.dataToMessageInfo w).miLabel := by
    rw [hlab, hwmi]; exact (Endp.label_mask w).symm
  have hq1 : Endp.ipcBufOf true x1 = some rp := by rw [hx1, Endp.ipcBufOf_copyRegs]; exact hrb
  obtain ⟨hOKc, -, -⟩ := J1.xferH
  have hu1 : ∀ k, k < 128 → Fl4Spec.inUserFrame (Endp.bufAddr rp k) σc := fun k hk => buf_frame_of_ok hOKc hkc hq1 k hk
  have hsrcL1 : ∀ j (hj : j < caps.length), ∃ ps, (caps[j]).2.1 = ps.bv ∧
      DestCap Z.th (L.mem s1) ps := by
    intro j hj
    obtain ⟨ps, rs, idx, cv, hps, hls, hsl, hxa, -⟩ := hok.2.1 j hj
    have hA : AbsSlot Z.th (ps.bv, idx) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
    have hne0 : Ipc.exAt extra j ≠ 0#u64 := by rw [hxa]; exact hA.isSlot.ne_zero J.xtop.rel.1
    obtain ⟨ps', idx', he', hth', hD'⟩ := hlive j (by have := hok.1; omega) hne0
    have e := cslotAddr_inj J.xtop.rel.1 hA (⟨ps', rfl, Or.inl hth'⟩ : AbsSlot Z.th (ps'.bv, idx'))
      (hxa.symm.trans he')
    exact ⟨ps', by rw [hsl]; exact congrArg Prod.fst e, hD'.same hS1⟩
  refine WP.spec_bind (transfer_capsJ (Z := Z.mv Z.G V1) (thT rcv hr) J1 hkc hq1 tag (Fl4Spec.dataToMessageInfo w)
    hlenw hlabw hok1.1 hok1.2.1 hsrcL1 hok1.2.2 ep rw hrwv hrwn hmr hu1) ?_
  rintro ⟨out, s2⟩ ⟨σt, mf, htc, hMi, hexc, hcu, he3, hlbt, hKC, hks2, ⟨G2, V2, J2⟩⟩
  simp only at hMi hexc hcu he3 hks2 J2
  show (do
    let s3 ← msg.set_msg_info st s2 rcv { out with length := n }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  refine WP.spec_bind (Endp.set_msg_info_specG (L := L) s2 rcv { out with length := n } (by show n.val < 128; omega)
    hcu (by show out.extra_caps.val < 4; omega)) ?_
  rintro s3 ⟨v, rfl, hv⟩
  refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ rcv _ badge) ?_
  rintro s4 rfl
  have hkt : σt.kheap rcv.bv = some (.tcb x1) := by
    rcases hKC.1 rcv.bv with e | ⟨r, cs, cs', h1, -⟩
    · rw [e, hkc]
    · rw [hkc] at h1; cases h1
  have hcopy' : Fl4Spec.copyMrs (Z := Unit) snd.bv (Endp.ipcBufOf false xs) rcv.bv (some rp)
      (Fl4Spec.dataToMessageInfo w).miLength σ = ({(n.bv, σc)}, False) := by
    rw [← hlenw]; exact hcopy
  have htc' : Fl4Spec.transferCaps (Z := Unit) (Fl4Spec.dataToMessageInfo w) caps epo rcv.bv (some rp) σc =
      ({(mf, σt)}, False) := by
    rcases hepo with rfl | ⟨rfl, rfl⟩
    · exact htc
    · rw [Endp.transferCaps_none _ _ _ _ (Ipc.noEp0_of_src hok1.2.1)]; exact htc
  have hspec := Endp.doIpcTransfer_grant hks hkr hf hrb epo badge.bv grant hlk hcopy' htc' hkt
  have hvx : v.bv = Fl4Spec.messageInfoToData
      ⟨n.bv, mf.miExtraCaps, mf.miCapsUnwrapped, (Fl4Spec.dataToMessageInfo w).miLabel⟩ := by
    rw [hv]
    show Fl4Spec.messageInfoToData ⟨n.bv, out.extra_caps.bv, out.caps_unwrapped.bv,
      out.label.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits⟩ = _
    rw [hexc, hMi.2.1, hMi.2.2, hlbt]
    congr 2
    show ((w >>> 12) &&& Fl4Spec.mask Fl4Spec.msgLabelBits) &&& Fl4Spec.mask Fl4Spec.msgLabelBits =
      (w >>> 12) &&& Fl4Spec.mask Fl4Spec.msgLabelBits
    rw [BitVec.and_assoc, BitVec.and_self]
  -- the message info
  have hI2 := J2.xtop.irelK J2.ks J2.buf
  have hX2 := reg_wr_irel J2.ip hI2 hr hkt Fl4Spec.msg_info_register (by decide) v
  obtain ⟨V3, J3⟩ := J2.regWrJ hr hkt Fl4Spec.msg_info_register v hX2
  rw [regIdx_msgInfo] at J3
  have hkt2 : (Notif.updK σt rcv.bv (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp [Notif.updK]
  -- the badge
  have hX4 := badge_wr_irel J3.ip (J3.xtop.irelK J3.ks J3.buf) hr hkt2 badge
  rw [badgeRegA_eq_regA] at hX4
  obtain ⟨V4, J4⟩ := J3.regWrJ hr hkt2 Fl4Spec.badge_register badge hX4
  rw [regIdx_badge] at J4
  have hfin : Notif.updK (Notif.updK σt rcv.bv (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      Notif.updK σt rcv.bv (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register
        (Fl4Spec.messageInfoToData ⟨n.bv, mf.miExtraCaps, mf.miCapsUnwrapped,
          (Fl4Spec.dataToMessageInfo w).miLabel⟩)) Fl4Spec.badge_register badge.bv)) := by
    simp only [Notif.updK, Function.update_idem]; rw [hvx]
  refine ⟨_, hspec, ?_, ⟨Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register
    (Fl4Spec.messageInfoToData ⟨n.bv, mf.miExtraCaps, mf.miCapsUnwrapped,
      (Fl4Spec.dataToMessageInfo w).miLabel⟩)) Fl4Spec.badge_register badge.bv,
    (by simp only [Notif.updK_kheap, Function.update_self]; try rfl), ?_⟩, G2, V4, by rw [← hfin]; exact J4⟩
  · intro p hp
    simp only [Notif.updK_kheap, Function.update_of_ne hp]
    rcases hKC.1 p with e | ⟨r, cs, cs', h1, h2⟩
    · left; rw [e, hkcf]; simp [Function.update_of_ne hp]
    · right; exact ⟨r, cs, cs', by rw [← h1, hkcf]; simp [Function.update_of_ne hp], h2⟩
  · rw [hx1, Endp.copyRegsTcb_other]; rfl

set_option maxHeartbeats 8000000 in
/-- **`do_ipc_transfer` at `J`, every case** (module docstring): a faulted
sender (`JAtZ.xferFaultJ`; [P] `hAT`, `hmax`, `htu` for a timeout with an
SC), the receiver without a buffer (`JAtZ.xferRegsGJ`), or with one
(`JAtZ.xferGrantJ`, granted caps included). The spec's outcome changes the
receiver's TCB in its user context, the sender's SC (a timeout fault's
consumed time) and CNodes (the granted caps' inserts) only. -/
theorem JAtZ.xferAllJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) 
    (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (grant : Bool)
    (epo : Option Fl4Spec.ObjRef) (ep badge : U64) (hepo : epo = some ep.bv ∨ (epo = none ∧ ep = 0#u64)) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      (∀ p, p ≠ rcv.bv → (∀ sc, xs.tcbSchedContext = some sc → p ≠ sc) → σ'.kheap p = σ.kheap p ∨
        ∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) ∧
      (∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch }) ∧
      JM (L := L) arI AR Z H Cs Ac Lst D a s' σ' ⦄ := by
  by_cases hf : xs.tcbFault = none
  · obtain ⟨hOK, hBC, -⟩ := J.xferH
    cases hrb : Endp.ipcBufOf true xr with
    | none =>
      refine WP.spec_mono (J.xferRegsGJ hOK hBC hs hr hne hks hkr hf hrb epo ep badge grant) ?_
      rintro s' ⟨h1, V, J'⟩
      refine ⟨_, h1, fun p hp _ => Or.inl (by simp [Notif.updK, hp]), ⟨Endp.xferTcb xr xs badge.bv,
        (by simp only [Notif.updK_kheap, Function.update_self]), ?_⟩, Z.G, V, J'⟩
      simp only [Endp.xferTcb]
      rw [Endp.copyRegsTcb_other]
      rfl
    | some rp =>
      refine WP.spec_mono (J.xferGrantJ hs hr hne hks hkr hf hrb epo ep badge grant hepo) ?_
      rintro s' ⟨σ', h1, h2, h3, h4⟩
      exact ⟨σ', h1, fun p hp _ => h2 p hp, h3, h4⟩
  · obtain ⟨f, hf'⟩ := Option.ne_none_iff_exists'.1 hf
    refine WP.spec_mono (J.xferFaultJ hs hr hne hks hkr hf' (fun _ _ _ _ => ⟨hAT, hmax, htu⟩)
      epo ep badge grant) ?_
    rintro s' ⟨σ', h1, h2, h3, V, h4⟩
    exact ⟨σ', h1, fun q hq hsc => Or.inl (h2 q hq (fun b sc _ h2 => hsc sc h2)), h3, Z.G, V, h4⟩

end

end

end Fl4Proofs.P3
