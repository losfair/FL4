/-
P3 (DESIGN.md §9), IPC: **`do_ipc_transfer` with a cap granted** (toward
XTopJointSendPushD's `JSendRecvHyp`), on `IRel` inside the dequeued interval
of a send to a waiting receiver, with the insert as a trace (IpcGrantTr).

* `copy_mrs_rgB`, `wr_reg_rg`, `updK_um_updK`: helpers.
* `do_ipc_transfer_grantG`: IpcGrantX's `do_ipc_transfer_grant` with the
  FL4 footprint (the receiver's registers, its buffer words, slot words) and
  the insert trace: no insert (the spec's outcome the start's up to user
  memory and the receiver's TCB, the slots kept) or one (`InsRec` at the
  state after the copy, the sources' and the receive slot's CNodes live at
  the start).
* `insWl`, `insWords_out`: the slot words an insert may change.
* `JAtZ.xferStepGJ`: the transfer step of the five send-to-receiver lemmas,
  any grant: P1 through the insert's slot words (`capw_bx`, split by
  `mixS`) and the rest (`blkX_bufw`), and the base `(yb, σy)` for the way
  back to `JAtZ` (the insert redone at the pre-dequeue `JAtZ` state by
  `JAtZ.insDJ`, the spec's outcome there patched by `capInsert_patch`), from
  which the writes are `CnW`/`KW` and the receiver's buffer words again.
-/
import Fl4Proofs.P3.XTopJointXferB
import Fl4Proofs.P3.XTopJointGrant
import Fl4Proofs.P3.IpcGrantTr
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section GrantG
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `copy_mrs` writes the receiver's registers and buffer words only. -/
theorem copy_mrs_rgB {T1 : Set U64} (hT : P1.TcbPlaced T1) {rcv : U64} (hr : rcv ∈ T1) {rw : U64}
    (hrw0 : rw ≠ 0#u64) (hal : ∀ i : U64, i.val < 128 → P1.Aligned (fl4BufA rw i)) {s : S} {snd : U64}
    (sw n : U64) :
    msg.copy_mrs st s snd sw rcv rw n ⦃ r => P1.WritesIn st s r.2 (Fl4Proofs.P3.XferBW T1 rw) ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (Fl4Proofs.P3.copy_mrs_loop0_rg (snd := snd) (n := n) hT hr (P1.WritesIn.refl s _)) ?_
  rintro ⟨s1, i⟩ h1
  have h1' : P1.WritesIn st s s1 (Fl4Proofs.P3.XferBW T1 rw) := h1.mono fun b hb => Or.inl hb
  simp only [hrw0, ↓reduceIte]
  by_cases hsw0 : sw = 0#u64
  · simp only [hsw0, ↓reduceIte]
    first | exact (WP.spec_ok _).2 h1' | (simp only [WP.spec_ok]; exact h1')
  · simp only [hsw0, ↓reduceIte]
    exact Fl4Proofs.P3.copy_mrs_loop1_rb hal (fun b hb => Or.inr hb) s1 h1' sw _ i

/-- A register write of a thread of `T1` lies in `XferRegW T1 ∅`. -/
theorem wr_reg_rg {T1 : Set U64} (hT1 : P1.TcbPlaced T1) {t : U64} (ht : t ∈ T1) (s : S) {r : U64}
    (hr : r.val < 384) (v : U64) : P1.WritesIn st s (L.wr s (regA t r) v) (XferRegW T1 ∅) := by
  have h1 := Fl4Proofs.P1.obj.Tcb.set_reg.rg (st := st) (s := s) (r := r) (v := v) hT1 ht hr
  have h2 := Fl4Proofs.P3.Endp.obj.Tcb.set_reg.spec (st := st) s t r v
  obtain ⟨s', -, h1', h2'⟩ := spec_exists (WP.spec_and h1 h2)
  rw [← h2']; exact h1'

theorem updK_um_updK (τ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (o o' : Fl4Spec.KernelObject)
    (u u' : Fl4Spec.Word → Fl4Spec.Word8) :
    Notif.updK (Endp.setUm (Notif.updK (Endp.setUm τ u') p o) u) p o' = Notif.updK (Endp.setUm τ u) p o' := by
  simp only [Notif.updK, Endp.setUm, Function.update_idem]

set_option maxHeartbeats 8000000 in
/-- **`do_ipc_transfer` with a receive buffer, caps granted, with the insert
trace** (module docstring). -/
theorem do_ipc_transfer_grantG (hH : IpcCore st N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (fun s σ => (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ ∧
      IpcBufCapOK σ) ∧ BufCover T B σ))
    (hBm : EpBufMapHyps st T E R B (fun s σ => (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ ∧
      IpcBufCapOK σ) ∧ BufCover T B σ))
    (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (hOK : IpcBufCapOK σ) (hBC : BufCover T B σ) (ep badge : U64) (grant : Bool)
    {T1 : Set U64} (hT1 : P1.TcbPlaced T1) (hr1 : rcv ∈ T1) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ (σ' : Fl4Spec.State Unit) (x' : Fl4Spec.Tcb),
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧
      SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => AllTF T b ∧ ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      KeepNC σ σ' rcv.bv ∧ σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch } ∧
      WritesIn st s s' (fun b => XferRegW T1 ∅ b ∨ RBufW ⟨rp⟩ b ∨ Sched.SlotWd th b) ∧
      ((∃ um, σ' = Notif.updK (Endp.setUm σ um) rcv.bv (.tcb x') ∧ SlotsSame th (L.mem s) (L.mem s')) ∨
       ∃ (s1 : S) (x1 : Fl4Spec.Tcb) (um0 : Fl4Spec.Word → Fl4Spec.Word8) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
         (slots : List Fl4Spec.CslotPtr) (sk' : S) (σc : Fl4Spec.State Unit) (um : Fl4Spec.Word → Fl4Spec.Word8),
         SlotsSame th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s ∧
         InsRec (L := L) th caps slots s1 (Notif.updK (Endp.setUm σ um0) rcv.bv (.tcb x1)) sk' σc ∧
         σ' = Notif.updK (Endp.setUm σc um) rcv.bv (.tcb x') ∧ SlotsSame th (L.mem sk') (L.mem s') ∧
         (∀ j (hj : j < caps.length), ∃ ps, (caps[j]).2.1 = ps.bv ∧ DestCap th (L.mem s) ps) ∧
         (∀ d ∈ slots, ∃ pd, d.1 = pd.bv ∧ DestCap th (L.mem s) pd)) ⦄ := by
  have hra := hP.tcb rcv hr
  have hxs := hR.at_tcb hs hks
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  have hIR := (IpcRel.ofSRN hR hSR).1
  obtain ⟨⟨⟨G, hB⟩, hBw⟩, -⟩ := hSR.1.1
  have hEH := hH.epHyps hP0
  have hSRb : (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ ∧ IpcBufCapOK σ) ∧
      BufCover T B σ := ⟨⟨hSR.1, hOK⟩, hBC⟩
  have hu := hBm.frame s σ rcv xr rp hR hSRb hr hkr hrb
  unfold ipc.do_ipc_transfer
  have hlb := lookup_buf_full s σ hB.2.1.1 hB.2.1.2.1 (RelTopB.tcbT hB hkr) hkr hOK true
  obtain ⟨x0, hk0, hbw⟩ := hBw.bw rcv hr
  rw [hkr] at hk0; cases hk0
  refine WP.spec_bind (WP.spec_and (hBm.lookupMap s σ rcv xr true rp hR hSRb hr hkr hrb) hlb) ?_
  rintro rw ⟨⟨hrw0, hmr⟩, hwl⟩
  have hrwe : rw = ⟨rp⟩ := by
    have hwb : rw.bv = rp := hwl.2 hbw rp hrb
    rw [← hwb]
  subst hrwe
  have hal : ∀ i : U64, i.val < 128 → P1.Aligned (fl4BufA ⟨rp⟩ i) := fun i hi => (hP.balign _ (hmr i hi)).1
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_send_buf hBf hBm s σ hR hSRb hs hks) ?_
  rintro sw hsw
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  have hn3 : tag.extra_caps.val ≤ 3 := by
    show tag.extra_caps.bv.toNat ≤ 3; rw [hext, hwmi]; exact extra_le3 w
  have hsb' : sw = 0#u64 ↔ ipcBufOf false xs = none := by
    rcases hsw with ⟨h1, h2⟩ | ⟨sp, h1, h2, -⟩
    · exact ⟨fun _ => h1, fun _ => h2⟩
    · rw [h1]; exact ⟨fun h => absurd h h2, fun h => by cases h⟩
  have hsm : ∀ sb, ipcBufOf false xs = some sb → BufMap B sw sb := by
    intro sb h
    rcases hsw with ⟨h1, -⟩ | ⟨sp, h1, -, h3⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h; exact h3
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sw tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ extra => ∃ caps,
        (if grant = true then Fl4Spec.NonDetE.catch (Fl4Spec.lookupExtraCaps (Z := Unit) snd.bv (ipcBufOf false xs)
          (Fl4Spec.dataToMessageInfo w)) (fun _ => pure []) else pure []) σ = ({(caps, σ)}, False) ∧
        ExtraOK th (L.mem s) extra caps ∧ ExtraLive th (L.mem s) (L.ksb s) extra ⦄ := by
    have hnl : ExtraLive th (L.mem s) (L.ksb s) ipc.NO_EXTRA_CAPS :=
      fun j hj hne => absurd (Ipc.exAt_none j hj) hne
    cases grant with
    | false =>
      rw [if_neg (by decide), WP.spec_ok]
      exact ⟨[], rfl, extraOK_none th _, hnl⟩
    | true =>
      rw [if_pos rfl]
      refine WP.spec_bind (WP.spec_and (lookup_extra_top hP0 hB hIR (hB.tcbT hks) sw (ipcBufOf false xs) hsb' hsm
        tag (Fl4Spec.dataToMessageInfo w) (by show tag.extra_caps.bv.toNat = _; rw [hext, hwmi]) hn3)
        (lookup_extra_live th s σ hB.2.1.1 hB.2.1.2.1 (hB.tcbT hks) sw tag)) ?_
      rintro r ⟨⟨caps, hc, hok⟩, hl⟩
      cases r with
      | Ok e => simp only [WP.spec_ok]; exact ⟨caps, by simp only [↓reduceIte]; exact hc, hok, hl _ rfl⟩
      | Err _ => simp only [WP.spec_ok]; exact ⟨caps, by simp only [↓reduceIte]; exact hc, hok, hnl⟩
  refine WP.spec_bind hex ?_
  rintro extra ⟨caps, hlk, hok, hlive⟩
  refine WP.spec_bind (WP.spec_and (copy_mrs_rel hEH hP s σ hR hSR.1 hs hr hne hks hkr hmr hrw0 hu hsw tag.length hle)
    (copy_mrs_rgB hT1 hr1 hrw0 hal sw tag.length (snd := snd))) ?_
  rintro ⟨n, s1⟩ ⟨⟨σc, hcopy, hkcf, hRc, hSc, hAc, hn, hWc, hEc⟩, hF1⟩
  simp only at hcopy hkcf hRc hSc hAc hn hWc hEc hF1
  set x1 := copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take tag.length.val) with hx1
  have hkc : σc.kheap rcv.bv = some (.tcb x1) := by rw [hkcf]; simp
  have hkco : ∀ p, p ≠ rcv.bv → σc.kheap p = σ.kheap p := fun p hp => by
    rw [hkcf]; simp [Function.update_of_ne hp]
  have hB1 : RelTopB (L := L) th G N T C E R B c s1 σc := hB.stableE hWc hEc
  have hN1 : NtfnStateRel N T (L.mem s1) σc :=
    ntfn_lift_rcv hP0.toC hSR.2 hRc hr (hAc.mono fun b hb => ⟨fun ⟨r, _, h'⟩ => hb.1 ⟨r, h'⟩, hb.2⟩) hkco hkr hkc
      (copyRegsTcb_state _ _ _)
  have hIR1 : IpcRel N T E R B (L.mem s1) σc := IpcRel.of hN1 hRc hSc.2.all
  have hSE1 : SRE st N T C E R B c s1 σc := hSc.1.2
  have hScb : (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s1 σc ∧ IpcBufCapOK σc) ∧
      BufCover T B σc := ⟨⟨hSc, Fl4Proofs.P3.ipcBufCapOK_epStep hOK hEc⟩, Fl4Proofs.P3.bufCover_epStep hBC hEc⟩
  have hS1 : SlotsSame th (L.mem s) (L.mem s1) :=
    slotsSame_of_iwords hB.1 hB.2.2.2.2.2.1 hWc (fun _ ha => EWrite.iwords ha)
  have hok1 := hok.of_same hS1
  have hrb1 : ipcBufOf true x1 = some rp := by rw [ipcBufOf_copyRegs]; exact hrb
  have hlenw : tag.length.bv = (Fl4Spec.dataToMessageInfo w).miLength := by rw [hlen, hwmi]
  have hlabw : tag.label.bv = (Fl4Spec.dataToMessageInfo w).miLabel := by
    rw [hlab, hwmi]; exact (label_mask w).symm
  refine WP.spec_bind (transfer_caps_topG hP0 hB1 hIR1 hSE1 tag (Fl4Spec.dataToMessageInfo w) hlenw hlabw hok1.1
    hok1.2.1 hok1.2.2 ep rcv ⟨rp⟩ (some rp) ⟨fun h => absurd h hrw0, fun h => by cases h⟩
    (fun rb h => by cases h; exact ⟨hmr, hBm.frame s1 σc rcv x1 rp hRc hScb hr hkc hrb1⟩)
    (fun rb h => by cases h; exact hBm.recvSlots s1 σc rcv x1 rp hRc hScb hr hkc hrb1)
    (fun rb h => by cases h; exact get_receive_slot_top hP0 hB1 hIR1.toE (hB1.tcbT hkc) hmr hrw0 caps extra)
    (fun rb h => by cases h; exact get_receive_slot_live th s1 σc hB1.2.1.1 hB1.2.1.2.1 (hB1.tcbT hkc) ⟨rp⟩)) ?_
  rintro ⟨out, s2⟩ ⟨σt, mf, htc, hMi, hexc, hIRt, hcu, he3, hlbt, hSEt, ⟨hKC, hWt⟩, ⟨G', hBt⟩, htr, hWr⟩
  simp only at hMi hexc hIRt hcu he3 hSEt hWt hBt htr hWr
  show (do
    let s3 ← msg.set_msg_info st s2 rcv { out with length := n }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  refine WP.spec_bind (set_msg_info_specG (L := L) s2 rcv { out with length := n } (by show n.val < 128; omega)
    hcu (by show out.extra_caps.val < 4; omega)) ?_
  rintro s3 ⟨v, hs3, hv⟩
  step with Fl4Proofs.P3.Endp.obj.Tcb.set_reg.spec as ⟨s4, hs4⟩
  subst hs3 hs4
  have hkt : σt.kheap rcv.bv = some (.tcb x1) := by
    rcases hKC.1 rcv.bv with e | ⟨r, cs, cs', h1, -⟩
    · rw [e, hkc]
    · rw [hkc] at h1; cases h1
  have hcopy' : Fl4Spec.copyMrs (Z := Unit) snd.bv (ipcBufOf false xs) rcv.bv (some rp)
      (Fl4Spec.dataToMessageInfo w).miLength σ = ({(n.bv, σc)}, False) := by
    rw [← hlenw]; exact hcopy
  have hspec := doIpcTransfer_grant hks hkr hf hrb (some ep.bv) badge.bv grant hlk hcopy' htc hkt
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
  -- the two register writes
  obtain ⟨hR2, hW2, hS2⟩ := write_reg_rel hP s2 _ hIRt.toE hr hkt Fl4Spec.msg_info_register v
  rw [regIdx_msgInfo] at hR2 hW2
  have hkt2 : (updK σt rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp
  obtain ⟨hR3, hW3, hS3⟩ := write_reg_rel hP _ _ hR2 hr hkt2 Fl4Spec.badge_register badge
  rw [regIdx_badge] at hR3 hW3
  have hfin : updK (updK σt rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      updK σt rcv.bv (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register (Fl4Spec.messageInfoToData
        ⟨n.bv, mf.miExtraCaps, mf.miCapsUnwrapped, (Fl4Spec.dataToMessageInfo w).miLabel⟩))
        Fl4Spec.badge_register badge.bv)) := by
    simp only [updK, Function.update_idem]; rw [hvx]
  rw [hfin] at hR3
  have hSRS2 : SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s2 σt :=
    ⟨⟨RelTopI.of_B (hSR.1.1.1.stableE hWc hEc) hBt hWt (fun b hb => by
        rcases hb with h | ⟨wp, hw, rfl⟩
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩)))))
      (fun b hb => by
        have hP := hSR.1.1.1.eplaced
        rcases hb with h | ⟨wp, hw, rfl⟩
        · exact Or.inr (slotWd_nobuf hB.2.2.2.2.2.1 hB.1 hP.tcb h)
        · exact Or.inr (NoBufW.out hP.tcb fun t ht => by have := hP.bt wp hw t ht; omega))
      hKC.vsKeep, hSEt⟩, ScRelM.of hIRt⟩
  have hSf := hEH.stable _ _ _ _ (hEH.stable _ _ _ _ hSRS2 hW2 hS2) hW3 hS3
  rw [hfin] at hSf
  have hA2 : Agree (L.mem s2) (L.mem (L.wr (L.wr s2 (regA rcv layout.reg.MSG_INFO) v) (regA rcv layout.reg.BADGE)
      badge)) (fun b => ¬ RcvReg rcv b) := by
    intro b hb hn'
    rw [← regIdx_msgInfo, ← regIdx_badge,
      rd_wr_ne (a_reg hra Fl4Spec.badge_register).1 hb (fun h => hn' ⟨Fl4Spec.badge_register, by rw [← h]⟩),
      rd_wr_ne (a_reg hra Fl4Spec.msg_info_register).1 hb (fun h => hn' ⟨Fl4Spec.msg_info_register, by rw [← h]⟩)]
  have hNf := ntfn_lift_rcv hP0.toC hIRt.toN hR3 hr (hA2.mono fun _ h => h.1)
    (fun p hp => by simp [updK, Function.update_of_ne hp]) hkt
    (by simp only [updK_kheap, Function.update_self]; rfl) (by rw [setReg_state, setReg_state])
  -- the register writes keep the slots and lie in the receiver's registers
  have hW24 : WritesIn st s2 (L.wr (L.wr s2 (regA rcv layout.reg.MSG_INFO) v) (regA rcv layout.reg.BADGE) badge)
      (XferRegW T1 ∅) :=
    ((wr_reg_rg hT1 hr1 s2 (by simp [layout.reg.MSG_INFO, layout.reg.RSI]) v).trans
      (wr_reg_rg hT1 hr1 _ (by simp [layout.reg.BADGE, layout.reg.RDI]) badge)).mono fun b hb => hb.elim id id
  have hS24 : SlotsSame th (L.mem s2)
      (L.mem (L.wr (L.wr s2 (regA rcv layout.reg.MSG_INFO) v) (regA rcv layout.reg.BADGE) badge)) := by
    have hm1 : P1.Aligned (regA rcv layout.reg.MSG_INFO) := by
      rw [← regIdx_msgInfo]; exact (a_reg hra _).1
    have hm2 : P1.Aligned (regA rcv layout.reg.BADGE) := by
      rw [← regIdx_badge]; exact (a_reg hra _).1
    refine slotsSame_of_iwords hBt.1 hBt.2.2.2.2.2.1 ((writesIn_wr (v := v) hm1).trans (writesIn_wr (v := badge) hm2))
      fun b hb => Or.inl ⟨rcv, hr, ?_⟩
    rcases hb with rfl | rfl
    · rw [← regIdx_msgInfo, regA_val hra (regIdx_lt _)]; have := regIdx_lt Fl4Spec.msg_info_register; omega
    · rw [← regIdx_badge, regA_val hra (regIdx_lt _)]; have := regIdx_lt Fl4Spec.badge_register; omega
  obtain ⟨um0, hσc⟩ : ∃ um, σc = Notif.updK (Endp.setUm σ um) rcv.bv (.tcb x1) := ⟨_, Fl4Proofs.P3.epStep_form hEc hkcf⟩
  refine ⟨_, _, hspec, hR3, ⟨hSf, hNf⟩, ?_, ?_, by simp only [updK_kheap, Function.update_self]; rfl,
    Fl4Proofs.P3.setReg2_eqA xr _ _ _ _ _ _, ?_, ?_⟩
  · rintro b hb ⟨⟨y, hy, hty⟩, hnr, hnb⟩
    rw [hA2 b hb hnr]
    have h12 : L.mem s2 b = L.mem s1 b := by
      refine hWt.mem_eq hb fun hfw => ?_
      rcases hfw with hsw' | hbw
      · obtain ⟨y', hy', g1, g2⟩ := slotWd_range hB.1 hsw'
        have := hty.range
        exact hB.2.2.2.2.2.1.slot b (Or.inl ⟨y, hy, by omega, by omega⟩) y' hy' ⟨g1, g2⟩
      · exact hnb hbw
    rw [h12]
    exact hAc b hb ⟨fun ⟨r, _, h'⟩ => hnr ⟨r, h'⟩, hnb⟩
  · intro p hp
    simp only [updK_kheap, Function.update_of_ne hp]
    rcases hKC.1 p with e | ⟨r, cs, cs', h1, h2⟩
    · left; rw [e, hkco p hp]
    · right; left; exact ⟨r, cs, cs', by rw [← hkco p hp]; exact h1, h2⟩
  · refine ((hF1.trans hWr).trans hW24).mono fun b hb => ?_
    rcases hb with (h | h) | h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases h with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · rcases htr with ⟨⟨um, hσt⟩, hSS⟩ | ⟨rb, slots, hrb', hsl, ⟨sk', σcI, hrec, ⟨um, hσt⟩, hSSk⟩, hDL⟩
    · left
      refine ⟨um, ?_, SlotsSame.trans' (SlotsSame.trans' hS1 hSS) hS24⟩
      rw [hσt, hσc]
      exact updK_um_updK σ rcv.bv _ _ um um0
    · right
      have hks1 : L.ksb s1 = L.ksb s := hWc.1
      refine ⟨s1, x1, um0, caps, slots, sk', σcI, um, hS1, hks1, hσc ▸ hrec, by rw [hσt], SlotsSame.trans' hSSk hS24,
        fun j hj => ?_, fun d hd => ?_⟩
      · obtain ⟨ps, rs, idx, cv, hps, hls, hsl', hxa, -⟩ := hok.2.1 j hj
        have hA : AbsSlot th (ps.bv, idx) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
        have hne0 : exAt extra j ≠ 0#u64 := by rw [hxa]; exact hA.isSlot.ne_zero hB.1
        obtain ⟨ps', idx', he', hth', hD'⟩ := hlive j (by have := hok.1; omega) hne0
        have e := cslotAddr_inj hB.1 hA (⟨ps', rfl, Or.inl hth'⟩ : AbsSlot th (ps'.bv, idx')) (hxa.symm.trans he')
        exact ⟨ps', by rw [hsl']; exact congrArg Prod.fst e, hD'⟩
      · obtain ⟨pd, h1, h2⟩ := hDL d hd
        exact ⟨pd, h1, h2.same (SlotsSame.symm' hS1)⟩

end GrantG

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The words an insert may change -/

section InsW
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {th : TypedHeap}

/-- The slot words `cdt::insert` from `src` into `dest` may change. -/
def insWl (m : U64 → U64) (src dest : U64) : List U64 :=
  [wordOf dest 0#u64, wordOf dest 8#u64, wordOf dest 16#u64, wordOf dest 24#u64,
    wordOf src 0#u64, wordOf src 8#u64, wordOf src 24#u64] ++
  (if nextOf m src = 0#u64 then [] else [wordOf (nextOf m src) 16#u64])

theorem insWords_out {s s' : S} {c srcC : capability.Cap} {src dest : U64}
    (h : InsWords (L := L) th s s' c srcC src dest) {a k : U64} (ha : IsSlot th a) (hk : Off k)
    (hn : wordOf a k ∉ insWl (L.mem s) src dest) : L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
  rw [h a ha k hk]
  by_cases h1 : a = dest
  · subst h1; exfalso; apply hn; rcases hk with rfl | rfl | rfl | rfl <;> simp [insWl]
  rw [if_neg h1]
  by_cases h2 : a = src
  · subst h2
    rw [if_pos rfl]
    rcases hk with rfl | rfl | rfl | rfl
    · exact (hn (by simp [insWl])).elim
    · exact (hn (by simp [insWl])).elim
    · cases hf : fullF srcC c <;> simp [lit_ne]
    · exact (hn (by simp [insWl])).elim
  rw [if_neg h2]
  by_cases h3 : nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src ∧ k = 16#u64
  · exfalso; apply hn; obtain ⟨h0, rfl, rfl⟩ := h3; simp [insWl, h0]
  · rw [if_neg h3]

end InsW


/-- A non-CNode object after a `KeepC` step was there before. -/
theorem keepC_back {σ σ' : Fl4Spec.State Unit} (h : KeepC σ σ') {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}
    (hq : σ'.kheap q = some o) (ho : ∀ r cs, o ≠ .cnode r cs) : σ.kheap q = some o := by
  rcases h q with e | ⟨r, cs, cs', h1, h2⟩
  · rw [← e]; exact hq
  · rw [hq] at h2; cases h2; exact absurd rfl (ho r cs')

/-! ## The transfer step with a grant at `J` -/

section XferG
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 64000000 in
/-- **The transfer step of `send_ipc` to a waiting receiver at `J`, any
grant** (module docstring): on `IRel` inside the dequeued interval
(`xferStepJ` without a receive buffer, `do_ipc_transfer_grantG` with one),
P1's hole by `xfer_all`/`blkX_bufw` (an insert's slot words first by
`capw_bx`, split by `mixS`); and a base `(y, σy)` for the way back to `JAtZ`:
`(s, σ)` without an insert, else FL4's insert redone at `s` (`JAtZ.insDJ`, the
same slot words as the actual insert's by `insWords_cong`) and the spec's
`cap_insert` at `σ` (the actual one's outcome patched, `capInsert_patch`),
from which the writes are again `CnW`/`KW` and the receiver's buffer words. -/
theorem JAtZ.xferStepGJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {e : U64} {ep0 : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint ep0)) (o : Fl4Spec.Endpoint)
    {s1 : S} (hR1 : EpStateRel Z.T Z.E Z.R Z.B (L.mem s1) (Notif.updK σ e.bv (.endpoint o)))
    (hS1 : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s1 (Notif.updK σ e.bv (.endpoint o)))
    (hW1 : P1.WritesIn st s s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1)
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (badge : U64) (grant : Bool) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    (h : P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X s1 Q Rq)
    (hB : P1.BoundInv st (P1.Heap.tcbs H) Ac s1)
    (hX : P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) s1)
    (hSc : P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s1)
    (hSg : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s1) :
    ipc.do_ipc_transfer st arI s1 a snd e badge grant rcv ⦃ s2 => ∃ (x' : Fl4Spec.Tcb)
      (um : Fl4Spec.Word → Fl4Spec.Word8) (y : S) (σy : Fl4Spec.State Unit) (G' : MdbGhost),
      JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac Lst D y a σy ∧
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some e.bv) badge.bv grant rcv.bv (Notif.updK σ e.bv (.endpoint o)) =
        ({((), Notif.updK (Endp.setUm (Notif.updK σy e.bv (.endpoint o)) um) rcv.bv (.tcb x'))}, False) ∧
      x' = { xr with tcbArch := x'.tcbArch } ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s2)
        (Notif.updK (Endp.setUm (Notif.updK σy e.bv (.endpoint o)) um) rcv.bv (.tcb x')) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2
        (Notif.updK (Endp.setUm (Notif.updK σy e.bv (.endpoint o)) um) rcv.bv (.tcb x')) ∧
      Agree (L.mem s1) (L.mem s2) (fun b => AllTF Z.T b ∧ ¬ RcvReg rcv b ∧ ¬ BufW Z.B b) ∧
      P1.WritesIn st y s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xr b) ∧
      P1.WritesIn st y s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) y b ∨ RcvBufW xr b) ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X s2 Q Rq ∧
      P1.BoundInv st (P1.Heap.tcbs H) Ac s2 ∧
      P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s2 ∧
      P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s2 ∧
      P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s2 ∧
      (∀ y' ∈ P1.Heap.tcbs H, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s2 (core.num.U64.wrapping_add y' K) = L.mem s1 (core.num.U64.wrapping_add y' K)) ∧
      L.ksb y = L.ksb s ∧ KeepCV σ σy ∧ CnK σ σy ∧
      (∀ q, (∀ r cs, σ.kheap q ≠ some (.cnode r cs)) → σy.kheap q = σ.kheap q) ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h.tcbs
  have hr1 : rcv ∈ P1.Heap.tcbs H := J.zH.1 rcv hr
  have hse : snd.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hre : rcv.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hks1 : (Notif.updK σ e.bv (.endpoint o)).kheap snd.bv = some (.tcb xs) := by simp [hse, hks]
  have hkr1 : (Notif.updK σ e.bv (.endpoint o)).kheap rcv.bv = some (.tcb xr) := by simp [hre, hkr]
  obtain ⟨hOK, hBC, -⟩ := J.xferH
  have hOK1 : Endp.IpcBufCapOK (Notif.updK σ e.bv (.endpoint o)) := ipcBufCapOK_epStep hOK (EpStep.ep hk)
  have hBC1 : Endp.BufCover Z.T Z.B (Notif.updK σ e.bv (.endpoint o)) := bufCover_epStep hBC (EpStep.ep hk)
  have hdth : Z.th rcv = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := (IpcRel.toSRN hI.1 hI.2).1.1
    exact Ipc.RelTopB.tcbT hB0' hkr
  have hUd := J.rbufU hr hdth hkr
  have hIF : IFrame (L := L) Z.th s s1 := IRel.iframe_of hI hW1 fun b hb => CnW.oobj hI.2.2.1 hb
  have cXr : ∀ {s' : S} {σ' : Fl4Spec.State Unit} {b : U64}, XferRegW (P1.Heap.tcbs H) ∅ b →
      CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s' σ' b := by
    intro s' σ' b hb
    rcases hb with ⟨y, hy, K, h1', h2', -, eb⟩ | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩)
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
  have kXr : ∀ {s' : S} {b : U64}, XferRegW (P1.Heap.tcbs H) ∅ b → P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
      (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s' b := by
    intro s' b hb
    rcases hb with ⟨y, hy, K, h1', h2', h3', eb⟩ | hb
    · exact Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩
    · exact absurd hb (Set.notMem_empty _)
  cases hrb : Endp.ipcBufOf true xr with
  | none =>
    refine WP.spec_mono (xferStepJ hP0 hP (hH.epHyps hP0) s1 a _ hR1 hS1 hOK1 hBC1 hs hr hne hks1 hkr1 hf e badge
      grant (Or.inr (Or.inr (Or.inr hrb))) hTP hr1 h hB hX hSc hSg
      (fun b hb => ⟨(hUd b hb).1.ksb hW1.1, (hUd b hb).2⟩)) ?_
    rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hSc2, hSg2, f2⟩
    have hN2 := ntfn_lift_rcv (x' := x2) hP0.toC hS1.2 hR2 hr hA2 (fun p hp => by simp [hp]) hkr1 (by simp)
      (by rw [hx2])
    exact ⟨x2, um2, s, σ, Z.G, J, e2, hx2, hR2, ⟨hS2.1, hN2⟩, hA2.mono fun b hb => ⟨hb.2.1, hb.2.2⟩,
      (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => hb.imp_left cXr),
      footW_trans (footW_of F1) (w2.mono fun b hb => hb.imp_left kXr), h2, hB2, hX2, hSc2, hSg2, f2, rfl,
      KeepCV.refl σ, CnK.refl σ, fun q _ => rfl⟩
  | some rp =>
    have hU' : ∀ b ∈ rbList ⟨rp⟩, P1.OutsideObjs st (P1.Heap.tcbs H) Cs s1 b ∧
        (∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧
        b ∉ P1.Heap.frame H := fun b hb =>
      ⟨(hUd b ⟨rp, hrb, mem_rbList.1 hb⟩).1.ksb hW1.1, (hUd b ⟨rp, hrb, mem_rbList.1 hb⟩).2⟩
    refine WP.spec_mono (do_ipc_transfer_grantG hH (epBufHyps_bufC Z.T) (epBufMapHyps_bufC hP0) hP0 hP s1 a _ hR1 hS1
      hs hr hne hks1 hkr1 hf hrb hOK1 hBC1 e badge grant hTP hr1) ?_
    rintro s2 ⟨σ', x', hspec, hR2, hS2, hA2, -, -, hx', hWg, htr⟩
    rcases htr with ⟨um, rfl, hSS⟩ | ⟨s1', x1, um0, caps, slots, sk', σc, um, hS1', hks1', hrec, rfl, hSSk, hsrcL, hDL⟩
    · -- no insert
      have hWg' : P1.WritesIn st s1 s2 (fun b => XferRegW (P1.Heap.tcbs H) ∅ b ∨ RBufW ⟨rp⟩ b) := by
        refine ⟨hWg.1, hWg.2.1, fun b hb hn => ?_⟩
        by_cases hsw : SlotWd Z.th b
        · obtain ⟨a', ha', k, hk', rfl⟩ := hsw
          exact SlotsSame.wd hSS ha' hk'
        · exact hWg.2.2 b hb fun h' => h'.elim (fun h' => hn (Or.inl h')) fun h' => h'.elim (fun h' => hn (Or.inr h')) hsw
      obtain ⟨h2, hB2, hX2, hSc2, hSg2, -, -, -, -, f2⟩ := blkX_bufw (l := rbList ⟨rp⟩) h hB hX hSc hSg hU'
        (hWg'.mono fun b hb => hb.imp_right mem_rbList.2)
      exact ⟨x', um, s, σ, Z.G, J, hspec, hx', hR2, hS2, hA2,
        (hW1.mono fun b hb => Or.inl hb).trans1 (hWg'.mono fun b hb => hb.imp cXr fun h' => ⟨rp, hrb, h'⟩),
        footW_trans (footW_of F1) (hWg'.mono fun b hb => hb.imp kXr fun h' => ⟨rp, hrb, h'⟩), h2, hB2, hX2, hSc2,
        hSg2, f2, rfl, KeepCV.refl σ, CnK.refl σ, fun q _ => rfl⟩
    · -- one insert: the base `(y, σy)`
      obtain ⟨cv, c', a', ps, pd, rs, rd, idx, idxd, sk, σk, hps, hpd, hls, hld, ⟨j, hj, hsl⟩, hslots, hsrcC1, hsnn,
        hdst1, hca, hcv, he', hcnn, hsh, hbd, hnu, hzb, hkey, hv, htu, huc, hnat, hSk, hiw, -, ⟨um1, hσk⟩, hci⟩ := hrec
      have hX0 := J.xtop
      obtain ⟨hPl, ⟨hSt, hV, hM, hC, hI'⟩, -, -, -, -, -⟩ := hX0.rel
      have hAs : AbsSlot Z.th (ps.bv, idx) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
      have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
      have hSs1 : SlotsSame Z.th (L.mem s) (L.mem s1') := SlotsSame.trans' hIF.1 hS1'
      have hSsk : SlotsSame Z.th (L.mem s) (L.mem sk) := SlotsSame.trans' hSs1 hSk
      have hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idx)) = ok cv := by
        rw [← SlotsSame.capAt hSs1 hAs.isSlot]; exact hsrcC1
      have hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null := by
        rw [← SlotsSame.capAt hSs1 hAd.isSlot]; exact hdst1
      have hsd : cslotAddr (ps.bv, idx) ≠ cslotAddr (pd.bv, idxd) := fun e0 => by
        rw [e0, hdst] at hsrcC; exact hsnn (eq_of_ok_eq hsrcC).symm
      have hsm : cslotAddr (ps.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, cv, hsrcC, hsnn⟩
      have hdnm : cslotAddr (pd.bv, idxd) ∉ Z.G.chains.flatten := fun h0 => by
        obtain ⟨-, c0, h0', hn0⟩ := (hM.members _).1 h0
        rw [hdst] at h0'; exact hn0 (eq_of_ok_eq h0').symm
      have hnxS : nextOf (L.mem s) (cslotAddr (ps.bv, idx)) = 0#u64 ∨
          (IsSlot Z.th (nextOf (L.mem s) (cslotAddr (ps.bv, idx))) ∧
            nextOf (L.mem s) (cslotAddr (ps.bv, idx)) ≠ cslotAddr (pd.bv, idxd) ∧
            nextOf (L.mem s) (cslotAddr (ps.bv, idx)) ≠ cslotAddr (ps.bv, idx)) := by
        rcases hM.next_mem hsm with h0 | ⟨h1', h2'⟩
        · exact Or.inl h0
        · exact Or.inr ⟨((hM.members _).1 h1').1, fun e0 => hdnm (e0 ▸ h1'), h2'⟩
      have hnxW : nextOf (L.mem s) (cslotAddr (ps.bv, idx)) = 0#u64 ∨
          IsSlot Z.th (nextOf (L.mem s) (cslotAddr (ps.bv, idx))) := hnxS.imp_right And.left
      have hut : isUt cv = true → ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr (ps.bv, idx)) := by
        intro hu0 y hy
        obtain ⟨z, hz⟩ := desc_tail_child hy
        exact hnu hu0 ((hC.has_child_iff hPl hAs).2 ⟨z, hz⟩)
      obtain ⟨ps', hps1, hDs⟩ := hsrcL j hj
      have eps : ps' = ps := P1.eq_of_bv (by rw [← hps1, hsl])
      rw [eps] at hDs
      obtain ⟨pd', hpd1, hDd⟩ := hDL (pd.bv, idxd) (by rw [hslots]; exact List.mem_singleton_self _)
      have epd : pd' = pd := P1.eq_of_bv hpd1.symm
      rw [epd] at hDd
      obtain ⟨y, -, ⟨⟨σy, hci', hKCV, hCnK, hksy, -, -, -, G', Jy⟩, hiwy⟩, hwy⟩ := spec_exists
        (WP.spec_and (WP.spec_and (J.insDJ hps hpd hls hld hsrcC hsnn hdst c' a' hca hcv he' hcnn hsh (Or.inl hbd) hut
          hzb hkey hv htu huc hnat (hDs.same (SlotsSame.symm' hIF.1)) (hDd.same (SlotsSame.symm' hIF.1))) (insert_mem hPl s c' _ _ hAs.isSlot hAd.isSlot hsd cv hsrcC hnxS))
          (insert_ws hPl s c' _ _ hAs.isSlot hAd.isSlot cv hsrcC hnxW))
      have hSy2 : SlotsSame Z.th (L.mem y) (L.mem s2) :=
        SlotsSame.trans' (insWords_cong hSsk hAs.isSlot hAd.isSlot hiwy hiw) hSSk
      -- the spec: the actual insert's outcome is `σy` patched
      obtain ⟨css, hkps, hwfs, hslS⟩ := hSt.cnode ps rs hps
      obtain ⟨csd, hkpd, hwfd, hslD⟩ := hSt.cnode pd rd hpd
      obtain ⟨c0, srcA, hc0, hcs0, -⟩ := hslS idx hls
      obtain ⟨c1, ac1, hc1, hcs1, hr1'⟩ := hslD idxd hld
      have hc1n : c1 = .Null := by
        have : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok c1 := hc1
        rw [hdst] at this; exact (eq_of_ok_eq this).symm
      subst hc1n
      have hac1 : ac1 = .nullCap := by rw [← hr1'.2]; rfl
      subst hac1
      have hne' : (ps.bv, idx) ≠ (pd.bv, idxd) := fun e0 => hsd (congrArg cslotAddr e0)
      have hpse : ps.bv ≠ e.bv := kheap_ne hkps hk (fun _ h1 h2 => by subst h1; cases h2)
      have hpde : pd.bv ≠ e.bv := kheap_ne hkpd hk (fun _ h1 h2 => by subst h1; cases h2)
      have hpsr : ps.bv ≠ rcv.bv := kheap_ne hkps hkr (fun _ h1 h2 => by subst h1; cases h2)
      have hpdr : pd.bv ≠ rcv.bv := kheap_ne hkpd hkr (fun _ h1 h2 => by subst h1; cases h2)
      have hτs : σk.kheap ps.bv = σ.kheap ps.bv := by rw [hσk]; simp [hpse, hpsr]
      have hτd : σk.kheap pd.bv = σ.kheap pd.bv := by rw [hσk]; simp [hpde, hpdr]
      have hτc : σk.cdt = σ.cdt := by rw [hσk]; rfl
      have hτo : σk.isOriginalCap = σ.isOriginalCap := by rw [hσk]; rfl
      obtain ⟨σ'', h1'', h2''⟩ := capInsert_patch a' hkps hwfs hls hcs0 hkpd hwfd hld hcs1 hne' hτs hτd hτc hτo
      obtain ⟨σ3, h13, h23⟩ := capInsert_patch a' hkps hwfs hls hcs0 hkpd hwfd hld hcs1 hne' rfl rfl rfl rfl
      have e1 : σ'' = σy := by
        rw [hci'] at h1''; have := congrArg Prod.fst h1''
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this; exact this.symm
      have e3 : σ3 = σy := by
        rw [hci'] at h13; have := congrArg Prod.fst h13
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this; exact this.symm
      subst e3 e1
      have hself : patchK (fun q => q = ps.bv ∨ q = pd.bv) σ'' σ = σ'' := patchK_self_of h13 h23
      have hσc : σc = patchK (fun q => q = ps.bv ∨ q = pd.bv) σ'' σk := by
        rw [hci] at h2''; have := congrArg Prod.fst h2''
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this; exact this
      have hrP : ¬ (rcv.bv = ps.bv ∨ rcv.bv = pd.bv) := fun h0 => h0.elim (fun h0 => hpsr h0.symm) fun h0 => hpdr h0.symm
      have heP : ¬ (e.bv = ps.bv ∨ e.bv = pd.bv) := fun h0 => h0.elim (fun h0 => hpse h0.symm) fun h0 => hpde h0.symm
      have hfin : Notif.updK (Endp.setUm σc um) rcv.bv (.tcb x') =
          Notif.updK (Endp.setUm (Notif.updK σ'' e.bv (.endpoint o)) um) rcv.bv (.tcb x') := by
        rw [hσc, hσk, patchK_setUm, patchK_updK _ _ hrP, patchK_setUm, patchK_updK _ _ heP, hself,
          Endp.setUm_setUm, updK_um_updK]
      rw [hfin] at hspec hR2 hS2
      have hksy' : L.ksb s = L.ksb y := hksy.symm
      have hzC : SzKeepC Z.C σ'' σ := fun sc _ x n hx =>
        ⟨x, hCnK.other hx (fun r cs h0 => by cases h0) (fun x h0 => by cases h0)⟩
      have hyk : ∀ q, (∀ r cs, σ.kheap q ≠ some (.cnode r cs)) → σ''.kheap q = σ.kheap q := by
        intro q hq
        rw [← hself, patchK_kheap]
        by_cases hq' : q = ps.bv ∨ q = pd.bv
        · rcases hq' with rfl | rfl
          · exact absurd hkps (hq _ _)
          · exact absurd hkpd (hq _ _)
        · rw [if_neg hq']
      -- P1: the insert's slot words first, by `capw_bx`
      set lI := insWl (L.mem sk) (cslotAddr (ps.bv, idx)) (cslotAddr (pd.bv, idxd)) with hlI
      have hnxk : nextOf (L.mem sk) (cslotAddr (ps.bv, idx)) = nextOf (L.mem s) (cslotAddr (ps.bv, idx)) := by
        unfold nextOf; rw [SlotsSame.wd hSsk hAs.isSlot off24]
      have hlW : ∀ b ∈ lI, SlotWd Z.th b := by
        intro b hb
        simp only [hlI, insWl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hb
        · exact ⟨_, hAd.isSlot, _, off0, rfl⟩
        · exact ⟨_, hAd.isSlot, _, off8, rfl⟩
        · exact ⟨_, hAd.isSlot, _, off16, rfl⟩
        · exact ⟨_, hAd.isSlot, _, off24, rfl⟩
        · exact ⟨_, hAs.isSlot, _, off0, rfl⟩
        · exact ⟨_, hAs.isSlot, _, off8, rfl⟩
        · exact ⟨_, hAs.isSlot, _, off24, rfl⟩
        · split at hb
          · simp at hb
          · rename_i h0
            simp only [List.mem_singleton] at hb
            subst hb
            rw [hnxk] at h0 ⊢
            exact ⟨_, hnxW.resolve_left h0, _, off16, rfl⟩
      have halI : ∀ b ∈ lI, P1.Aligned b := fun b hb => by
        obtain ⟨a', ha', k, hk', rfl⟩ := hlW b hb
        exact slot_word_aligned hPl ha' hk'
      have hSC := J.slotCapW (fun t ht K hK => P1.tlow_slots t ht K hK)
      obtain ⟨hu1, hBu, hXu, hScu, hSgu, -, -, -, -, fu, -⟩ := P1.capw_bx h hB hX hSc hSg
        (mixS_from (s := s1) (t := s2) halI) fun b hb => hSC b (hlW b hb)
      have hS1k : SlotsSame Z.th (L.mem s1) (L.mem sk) := SlotsSame.trans' hS1' hSk
      have hwu : P1.WritesIn st (mixS (L := L) s1 s2 lI) s2
          (fun b => XferRegW (P1.Heap.tcbs H) ∅ b ∨ b ∈ rbList ⟨rp⟩) := by
        refine ⟨by rw [mixS_ksb]; exact hWg.1, by rw [mixS_cpu]; exact hWg.2.1, fun b hb hn => ?_⟩
        rw [mixS_mem s1 s2 lI halI hb]
        split
        · rfl
        · rename_i hbl
          by_cases hsw : SlotWd Z.th b
          · obtain ⟨a', ha', k, hk', rfl⟩ := hsw
            rw [SlotsSame.wd hSSk ha' hk', insWords_out hiw ha' hk' hbl]
            exact SlotsSame.wd hS1k ha' hk'
          · exact hWg.2.2 b hb fun h' => h'.elim (fun h' => hn (Or.inl h'))
              fun h' => h'.elim (fun h' => hn (Or.inr (mem_rbList.2 h'))) hsw
      obtain ⟨h2, hB2, hX2, hSc2, hSg2, -, -, -, -, f2⟩ := blkX_bufw (l := rbList ⟨rp⟩) hu1 hBu hXu hScu hSgu
        (fun b hb => ⟨(hU' b hb).1.ksb (mixS_ksb s1 s2 lI), (hU' b hb).2⟩) hwu
      refine ⟨x', um, y, σ'', G', Jy, hspec, hx', hR2, hS2, hA2, ⟨?_, ?_, fun b hb hn => ?_⟩,
        ⟨?_, ?_, fun b hb hn => ?_⟩, h2, hB2, hX2, hSc2, hSg2,
        fun y' hy' K h1' h2' h3' => (f2 y' hy' K h1' h2' h3').trans (fu y' hy' K (by omega) h2' h3'), hksy, hKCV, hCnK,
        hyk⟩
      · exact hWg.1.trans (hW1.1.trans hksy')
      · exact hWg.2.1.trans (hW1.2.1.trans hwy.2.1.symm)
      · by_cases hsw : SlotWd Z.th b
        · obtain ⟨a', ha', k, hk', rfl⟩ := hsw
          exact SlotsSame.wd hSy2 ha' hk'
        · rw [hwy.2.2 b hb hsw, hWg.2.2 b hb ?_]
          · exact hW1.2.2 b hb fun hc => hn (Or.inl (cnW_back hksy' hzC hc))
          · rintro (h' | h' | h')
            · exact hn (Or.inl (cXr h'))
            · exact hn (Or.inr ⟨rp, hrb, h'⟩)
            · exact hsw h'
      · exact hWg.1.trans (hW1.1.trans hksy')
      · exact hWg.2.1.trans (hW1.2.1.trans hwy.2.1.symm)
      · by_cases hsw : SlotWd Z.th b
        · obtain ⟨a', ha', k, hk', rfl⟩ := hsw
          exact SlotsSame.wd hSy2 ha' hk'
        · rw [hwy.2.2 b hb hsw, hWg.2.2 b hb ?_]
          · exact F1.2.2 b hb fun hc => hn (Or.inl (P1.KW.ksb hksy' hc))
          · rintro (h' | h' | h')
            · exact hn (Or.inl (kXr h'))
            · exact hn (Or.inr ⟨rp, hrb, h'⟩)
            · exact hsw h'

end XferG

end

end Fl4Proofs.P3
